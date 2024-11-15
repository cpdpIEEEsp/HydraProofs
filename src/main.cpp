#include <stdio.h>
//#include <mcl/bn256.hpp>
#include <mcl/bls12_381.hpp>
//#include <mcl/bn.h>
#include <vector>
#include <polynomial.h>
#include <math.h>
#include "MLP.h"
#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include <time.h>
#include "mimc.h"
#include "quantization.h"
#include "GKR.h"
#include <time.h>
#include <chrono>
#include "utils.hpp"
#include "pol_verifier.h"
#include "elliptic_curves.h"
#include "Poly_Commit.h"
#include "Aggr.h"
#include <thread>
#include "OpenAll.cpp"

#include <chrono>

using namespace std::chrono;

using namespace mcl::bn;

#define F Fr


#define F_ONE (Fr::one())
#define F_ZERO (Fr(0))
extern int partitions;
using namespace std;
double proving_time;
double verification_time;
int comm_size;

double total_time;
double range_proof_time = 0.0;
struct _temp{
	vector<int> v;
};

int threads = 1;
unsigned long int mul_counter = 0;
double Forward_propagation;
double dx_computation;
double gradients_computation;
double range_proof_verification_time;
int range_proof_size;
vector<int> predicates_size;
vector<struct proof> Transcript;

/*
vector<vector<F>> transpose(vector<vector<F>> M){
	vector<vector<F>> tM;
	tM.resize(M[0].size());
	for(int i = 0; i < tM.size(); i++){
		tM[i].resize(M.size());
	}
	for(int i = 0; i < tM.size(); i++){
		for(int j = 0; j < tM[0].size(); j++){
			tM[i][j] = M[j][i];
		}
	}
	return tM;
}
*/

vector<vector<F>> prepare_matrixes(vector<vector<F>> M1, vector<vector<F>> M2, vector<F> r1, vector<F> r2){
	vector<vector<F>> V(2);
	vector<vector<F>> M = _transpose(M1);

	V[0] = (prepare_matrix(M,r1));

	M = _transpose(M2);
	
	V[1] = (prepare_matrix(M,r2));
	
	return V;

}

vector<F> generate_randomness(int size, F seed){
	vector<F> r;
	
	F num = seed;
	for(int i = 0; i < size; i++){
		num = mimc_hash(num,seed);
		r.push_back(num);
	}
	/*
	for(int i = 0; i < size; i++){
		F num = F(0);
		num.setByCSPRNG();
		r.push_back(num);
	}
	*/
	return r;
}


struct proof generate_3product_sumcheck_proof_naive(vector<F> v1, vector<F> v2, vector<F> v3, vector<F> r){
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())),F(0));
	vector<cubic_poly> p;
	for(int i = 0; i < r.size(); i++){
		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		linear_poly l1,l2,l3;
		
		int L = 1 << (r.size() -1- i);
		for(int j = 0; j < L; j++){
			if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
				l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
				//q1 = quadratic_poly()
				l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
				l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
				temp_poly = l1*l2*l3;
				poly = poly + temp_poly;

			}
			v1[j] = (F(1)-r[i])*v1[2*j] + r[i]*v1[2*j+1];
			if(v2[2*j] == F(0) && v2[2*j+1] == F(0)){
				v2[j] = F(0);
				v3[j] = F(1);
			}else{

				v2[j] = v2[2*j] + r[i]*(v2[2*j+1]-v2[2*j]);
				v3[j] = v3[2*j] + r[i]*(v3[2*j+1]-v3[2*j]);	

			}
		}
		p.push_back(poly);
	}
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v1[0]);

	return Pr;
}

void _generate_3product_sumcheck_proof_folded(F* v1, F* v2, F* v3,F* new_v1,F* new_v2,F* new_v3, cubic_poly &poly,F sum, F rand, int idx, int L ){
	
 	int size = L/threads;
	int pos = idx*size;
	linear_poly l1,l2,l3;
	
	cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
	for(int j = pos; j < pos+size; j++){
		if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			//q1 = quadratic_poly()
			F coef = v2[2*j+1] - v2[2*j];
			l2 = linear_poly(coef,v2[2*j]);
			l3 = linear_poly(-coef,sum - v2[2*j]);
			//l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
			temp_poly = l1*l2*l3;
			poly = poly + temp_poly;
		}
		new_v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
		new_v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
		new_v3[j] = sum - new_v2[j];
	}
}


struct proof generate_3product_sumcheck_proof_folded(vector<F> &_v1, vector<F> &_v2, vector<F> &_v3,F sum,F previous_r){
	
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(_v1.size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;

	// Convert to data arrays
	F *v1 = _v1.data();
	F *v2 = _v2.data();
	F *v3 = _v3.data();


	for(int i = 0; i < rounds; i++){
		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		if(threads == 1  || 1 << (rounds - 1-i) <= 1<<14){
			cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3;
			
			int L = 1 << (rounds -1- i);
			for(int j = 0; j < L; j++){
				if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
					l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
					//q1 = quadratic_poly()
					F coef = v2[2*j+1] - v2[2*j];
					
					l2 = linear_poly(coef,v2[2*j]);
					l3 = linear_poly(-coef,sum - v2[2*j]);
					temp_poly = l1*l2*l3;
					poly = poly + temp_poly;

				}
				v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
				v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
				v3[j] = sum - v2[j];
			}
		}else{

			int L = 1 << (rounds -1- i);
			
			F *new_v1 = (F *)malloc(L*sizeof(F));
			F *new_v2 = (F *)malloc(L*sizeof(F));
			F *new_v3 = (F *)malloc(L*sizeof(F));
			
			//vector<F> new_v1(L),new_v2(L),new_v3(L);
			vector<cubic_poly> _poly(threads);
			thread worker[threads];
			for(int j = 0; j < threads; j++){
				_poly[j] = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			}

			for(int j = 0; j < threads; j++){
				//worker[i](_generate_2product_sumcheck,ref(v1),ref(v2),ref(_poly[i]),rand,i,L);
				//worker.push_back( std::async(&_generate_3product_sumcheck_proof_folded,ref(v1),ref(v2),ref(v3),ref(new_v1),ref(new_v2),ref(new_v3),ref(_poly[j]),sum,rand,j,L));
				worker[j] = thread(&_generate_3product_sumcheck_proof_folded,(v1),(v2),(v3),(new_v1),(new_v2),(new_v3),ref(_poly[j]),sum,rand,j,L);
				//worker[j] = thread([&](){_generate_3product_sumcheck_proof_folded((v1),(v2),(v3),(new_v1),(new_v2),(new_v3),(_poly[j]),sum,rand,j,L);});
				//thread th(_generate_3product_sumcheck_proof_folded,ref(v1),ref(v2),ref(v3),ref(new_v1),ref(new_v2),ref(new_v3),ref(_poly[j]),sum,rand,j,L);
				//worker.push_back(move(th));
			}
			for(int j = 0; j < threads; j++){
				worker[j].join();
				poly = poly+ _poly[j];
			}
			//copy(v1.begin(),v1.begin()+new_v1.size(),new_v1.begin());
			//copy(v2.begin(),v2.begin()+new_v2.size(),new_v2.begin());
			//copy(v3.begin(),v3.begin()+new_v3.size(),new_v3.begin());
			
			v1 = new_v1;
			v2 = new_v2;
			v3 = new_v3;

		}
		r.push_back(rand);
		vector<F> input;
		input.push_back(rand);
		input.push_back(poly.a);
		input.push_back(poly.b);
		input.push_back(poly.c);
		input.push_back(poly.d);
		vector<vector<F>> temp = mimc_multihash3(input);
		Pr.w_hashes.push_back(temp);
		rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		p.push_back(poly);
	}
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v1[0]);

	return Pr;
}

void _generate_3product_sumcheck(F* v1,F* v2,F* v3,F* new_v1,F* new_v2, F* new_v3, cubic_poly &poly, F rand, int idx, int L){
	int size = L/threads;
	int pos = idx*size;
	linear_poly l1,l2,l3;
	cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);

	

	for(int j = pos; j < pos+size; j++){
		if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			//q1 = quadratic_poly()
			F coef = v2[2*j+1] - v2[2*j];
			l2 = linear_poly(coef,v2[2*j]);
			l3 = linear_poly(-coef,F(1) - v2[2*j]);
			temp_poly = l1*l2*l3;
			poly = poly + temp_poly;
		}
		new_v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
		if(v2[2*j] == F(0) && v2[2*j+1] == F(0)){
			new_v2[j] = F(0);
			new_v3[j] = F(1);
		}else{
			new_v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
			new_v3[j] = F(1)-new_v2[j];//(1-r[i])*v3[2*j] + r[i]*v3[2*j+1];	

		}
	}
}

struct proof generate_3product_sumcheck_proof(vector<F> &_v1, vector<F> &_v2, vector<F> &_v3,F previous_r){
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(_v1.size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;
	F *v1 = _v1.data();
	F *v2 = _v2.data();
	//F *v3 = _v3.data();
	F *v3 = (F *)malloc(_v2.size()/2 * sizeof(F));
	for(int i = 0; i < rounds; i++){
		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		if(threads == 1  || 1 << (rounds - 1-i) <= 1<<10){
			cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3;
			
			int L = 1 << (rounds -1- i);
			for(int j = 0; j < L; j++){
				if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
					l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
					//q1 = quadratic_poly()
					F coef = v2[2*j+1] - v2[2*j];
					l2 = linear_poly(coef,v2[2*j]);
					l3 = linear_poly(-coef,F(1) - v2[2*j]);
					temp_poly = l1*l2*l3;
					poly = poly + temp_poly;

				}
				v1[j] = (F(1)-rand)*v1[2*j] + rand*v1[2*j+1];
				if(v2[2*j] == F(0) && v2[2*j+1] == F(0)){
					v2[j] = F(0);
					v3[j] = F(1);
				}else{
					v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
					v3[j] = F(1)-v2[j];//(1-r[i])*v3[2*j] + r[i]*v3[2*j+1];	

				}
			}

		}else{
			
			int L = 1 << (rounds -1- i);
			

			F *new_v1 = (F *)malloc(L*sizeof(F));
			F *new_v2 = (F *)malloc(L*sizeof(F));
			F *new_v3 = (F *)malloc(L*sizeof(F));
			
			vector<cubic_poly> _poly(threads);
			thread worker[threads];
			for(int j = 0; j < threads; j++){
				_poly[j] = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			}
			for(int j = 0; j < threads; j++){
				//worker[i](_generate_2product_sumcheck,ref(v1),ref(v2),ref(_poly[i]),rand,i,L);
				worker[j] = thread(&_generate_3product_sumcheck,(v1),(v2),(v3),(new_v1),(new_v2),(new_v3),ref(_poly[j]),rand,j,L);
				//thread th(_generate_3product_sumcheck_proof_folded,ref(v1),ref(v2),ref(v3),ref(new_v1),ref(new_v2),ref(new_v3),ref(_poly[j]),sum,rand,j,L);
				//worker.push_back(move(th));
			}

			for(int j = 0; j < threads; j++){
				worker[j].join();
				poly = poly+ _poly[j];
			}
			v1 = new_v1;
			v2 = new_v2;
			v3 = new_v3;

		}
		r.push_back(rand);
		vector<F> input;
		input.push_back(rand);
		input.push_back(poly.a);
		input.push_back(poly.b);
		input.push_back(poly.c);
		input.push_back(poly.d);
		vector<vector<F>> temp = mimc_multihash3(input);
		Pr.w_hashes.push_back(temp);
		rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		p.push_back(poly);
	}
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v1[0]);

	return Pr;
}


void _generate_norm_sumcheck_proof(F **M,F **temp_M,vector<vector<F>> &_M, vector<F> &beta, quadratic_poly &poly, F rand,int idx, int L,int i ){
	int size = _M.size()/threads;
	int pos = idx*size;
	quadratic_poly temp_poly;
	
	for(int k = pos; k < size+pos; k++){
		temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		for(int j = 0; j < L; j++){
			if(i == 0){
				F diff = _M[k][2*j + 1] - _M[k][2*j];
				temp_poly = temp_poly + quadratic_poly(diff*diff,F(2)*diff*_M[k][2*j],_M[k][2*j]*_M[k][2*j]);
				temp_M[k][j] = _M[k][2*j] + rand*(diff);			
			}else{
				F diff = M[k][2*j + 1] - M[k][2*j];
				temp_poly = temp_poly + quadratic_poly(diff*diff,F(2)*diff*M[k][2*j],M[k][2*j]*M[k][2*j]);
				temp_M[k][j] = M[k][2*j] + rand*(diff);	
			}

		}
		poly = poly +  quadratic_poly(beta[k] * temp_poly.a,beta[k] * temp_poly.b,beta[k] * temp_poly.c);
	}
}


struct proof generate_norm_sumcheck_proof(vector<vector<F>> &_M,vector<F> &beta, F previous_r){
	struct proof Pr;
	vector<F> r;// = generate_randomness(int(log2(v1.size())));
	F rand = mimc_hash(previous_r,F(0));
	vector<quadratic_poly> p;
	int rounds = int(log2(_M[0].size()));

	F **M = (F **)malloc(_M.size()*sizeof(F*));
	for(int i = 0; i < _M.size(); i++){
		M[i] = (F *)malloc(_M[0].size()*sizeof(F)/2);
	}

	auto ts = high_resolution_clock::now();

	
	for(int i = 0; i < rounds; i++){
		quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		linear_poly l1,l2;
		int L = 1 << (rounds - 1-i);
		if(threads == 1 || L < 1<<9){
			for(int k = 0; k < _M.size(); k++){
				temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
				for(int j = 0; j < L; j++){
					if(i == 0){
						F diff = _M[k][2*j + 1] - _M[k][2*j];
						temp_poly = temp_poly + quadratic_poly(diff*diff,F(2)*diff*_M[k][2*j],_M[k][2*j]*_M[k][2*j]);
						M[k][j] = _M[k][2*j] + rand*(diff);
					}else{
						F diff = M[k][2*j + 1] - M[k][2*j];
						temp_poly = temp_poly + quadratic_poly(diff*diff,F(2)*diff*M[k][2*j],M[k][2*j]*M[k][2*j]);
						M[k][j] = M[k][2*j] + rand*(diff);
					}
				}
				poly = poly +  quadratic_poly(beta[k] * temp_poly.a,beta[k] * temp_poly.b,beta[k] * temp_poly.c);
			}
		}else{
			F **temp_M = (F **)malloc(_M.size()*sizeof(F*));
			vector<quadratic_poly> _poly(threads);
			for(int j = 0; j < threads; j++){
				_poly[j] = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			}
			for(int j = 0; j < _M.size(); j++){
				temp_M[j] = (F *)malloc(L*sizeof(F));
			}
			thread worker[threads];
			for(int j = 0; j < threads; j++){
				worker[j] = thread(&_generate_norm_sumcheck_proof,M,temp_M,ref(_M),ref(beta),ref(_poly[j]),rand,j,L,i);
			}
			for(int j = 0; j < threads; j++){
				worker[j].join();
			}
			for(int j = 0; j < threads; j++){
				poly = poly + _poly[j];
			}
			M = temp_M;
			for(int j = 0; j < _M.size(); j++){
				M[j] = temp_M[j];
			}


		}
		

		r.push_back(rand);
		vector<F> input;
		input.push_back(rand);
		input.push_back(poly.a);
		input.push_back(poly.b);
		input.push_back(poly.c);
		vector<vector<F>> temp = mimc_multihash3(input);
		Pr.w_hashes.push_back(temp);
		rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		p.push_back(poly);
	}
	auto te = high_resolution_clock::now();
	auto tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;

	F eval = F(0);
	for(int i = 0; i < beta.size(); i++){
		eval += beta[i]*M[i][0];
	}
	Pr.vr.push_back(eval);
	Pr.vr.push_back(eval);
	Pr.q_poly = p;
	Pr.randomness.push_back(r);
	return Pr;
 }




void _generate_2product_sumcheck(F *v1,vector<F> &_v1, F *v2, vector<F> &_v2,F *new_v1,F *new_v2,quadratic_poly &poly,F rand,int idx,int L,int i){
	
	int size = L/threads;
	
	int pos = idx*size;
	
	linear_poly l1,l2;
	quadratic_poly temp_poly;
	for(int j = pos; j < pos + size; j++){
		if(i == 0){
			l1 = linear_poly(_v1[2*j+1] - _v1[2*j],_v1[2*j]);
			l2 = linear_poly(_v2[2*j+1] - _v2[2*j],_v2[2*j]);
			temp_poly = l1*l2;
			poly = poly + temp_poly;
			new_v1[j] = _v1[2*j] + rand*(_v1[2*j+1]-_v1[2*j]);
			new_v2[j] = _v2[2*j] + rand*(_v2[2*j+1]-_v2[2*j]);
		
		}else{
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
			temp_poly = l1*l2;
			poly = poly + temp_poly;
			new_v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
			new_v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
		}
		
	}
}


struct proof generate_2product_sumcheck_proof(vector<F> &_v1, vector<F> &_v2, F previous_r){
	struct proof Pr;
	vector<F> r;// = generate_randomness(int(log2(v1.size())));
	F rand = mimc_hash(previous_r,F(0));
	vector<quadratic_poly> p;
	int rounds = int(log2(_v1.size()));
	
	F *v1 = (F *)malloc(_v1.size()*sizeof(F)/2);
	F *v2 = (F *)malloc(_v2.size()*sizeof(F)/2);


	for(int i = 0; i < rounds; i++){
		quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		if(threads == 1 || (1 << (rounds - 1-i)) <= threads){
			quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2;
			int L = 1 << (rounds - 1-i);
			for(int j = 0; j < L; j++){
				if(i== 0){
					l1 = linear_poly(_v1[2*j+1] - _v1[2*j],_v1[2*j]);
					l2 = linear_poly(_v2[2*j+1] - _v2[2*j],_v2[2*j]);
					temp_poly = l1*l2;
					poly = poly + temp_poly;
					v1[j] = _v1[2*j] + rand*(_v1[2*j+1]-_v1[2*j]);
					v2[j] = _v2[2*j] + rand*(_v2[2*j+1]-_v2[2*j]);
					
				}else{
					l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
					l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
					temp_poly = l1*l2;
					poly = poly + temp_poly;
					v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
					v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
				
				}
				
			}
		}else{
			
			vector<quadratic_poly> _poly(threads);
			thread worker[threads];
			int L = 1 << (rounds - 1-i);
			F *new_v1 = (F *)malloc(L*sizeof(F));
			F *new_v2= (F *)malloc(L*sizeof(F));
			
			for(int j = 0; j < _poly.size(); j++){
				_poly[j] = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			}
			for(int j = 0; j < threads; j++){
				//worker[i](_generate_2product_sumcheck,ref(v1),ref(v2),ref(_poly[i]),rand,i,L);
				worker[j] = thread(&_generate_2product_sumcheck,v1,ref(_v1),v2,ref(_v2),new_v1,new_v2,ref(_poly[j]),rand,j,L,i);
			}
			for(int j = 0; j < threads; j++){
				worker[j].join();
				poly = poly+ _poly[j];
			}
			v1 = new_v1;
			v2 = new_v2;
				
		}
		r.push_back(rand);
		vector<F> input;
		input.push_back(rand);
		input.push_back(poly.a);
		input.push_back(poly.b);
		input.push_back(poly.c);
		vector<vector<F>> temp = mimc_multihash3(input);
		Pr.w_hashes.push_back(temp);
		rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		p.push_back(poly);
	}

	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v2[0]);
	Pr.q_poly = p;
	Pr.randomness.push_back(r);
	return Pr;
 }



struct proof prove_norm(vector<vector<F>> &M, vector<F> r, F norm_eval){
	
	vector<F> beta;
	precompute_beta(r,beta);
	proof P  = generate_norm_sumcheck_proof(M,beta, r[0]);
	if(P.q_poly[0].eval(0) + P.q_poly[0].eval(1) != norm_eval){
		printf("Error in norm check\n");
		exit(-1);
	}
	P.type = -1;
	return P;
}


struct proof prove_ifft(vector<F> M){
	F scale;
	F::inv(scale,M.size());
	vector<F> r1 = generate_randomness(int(log2(M.size())),F(0));
	
    vector<F> Fg(M.size());
    phiGInit(Fg,r1.begin(),scale,r1.size(),true);

    struct proof Pr = generate_2product_sumcheck_proof(Fg,M,r1[r1.size()-1]);
	Pr.randomness.push_back(r1);
	Pr.type = MATMUL_PROOF;
	return Pr;

}

struct proof prove_ifft_matrix(vector<vector<F>> M, vector<F> r, F previous_sum){
	F scale;
	F::inv(scale,M[0].size());
	vector<F> r1,r2;
	

	
	for(int i = 0; i < int(log2(M[0].size()))-1; i++){
		r2.push_back(r[i]);
	}
	r2.push_back(r[r.size()-1]);
	for(int i = 0; i < int(log2(M.size())); i++){
		r1.push_back(r[i+int(log2(M[0].size()))-1]);
	}
	vector<F> Fg(M[0].size());
	clock_t start,end;
	start = clock();
	vector<F> arr = prepare_matrix((transpose(M)),r1);
	phiGInit(Fg,r2.begin(),scale,r2.size(),true);

	struct proof Pr = generate_2product_sumcheck_proof(Fg,arr,r[r.size()-1]);
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;

	if(previous_sum != Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1)){
		printf("Error in ifft\n");
		exit(-1);
	}
	
	Pr.randomness.push_back(r1);
	Pr.randomness.push_back(r2);
	Pr.type = MATMUL_PROOF;
	return Pr;
}

struct proof prove_fft(vector<F> M){
	M.resize(2*M.size(),F(0));
	vector<F> r1 = generate_randomness(int(log2(M.size())),F(0));
	
	vector<F> Fg1(M.size()); 
	phiGInit(Fg1,r1.begin(),F(1),r1.size(),false);
	
	struct proof Pr = generate_2product_sumcheck_proof(Fg1,M,r1[r1.size()-1]);
	Pr.randomness.push_back(r1);
	Pr.type = MATMUL_PROOF;
	
	return Pr;

}

struct proof prove_fft_matrix(vector<vector<F>> M, vector<F> r, F previous_sum){
	for(int i  = 0; i < M.size(); i++){
		M[i].resize(2*M[i].size(),F(0));
	}
	

	vector<F> r1,r2;
	for(int i = 0; i < int(log2(M[0].size())); i++){
		r2.push_back(r[i]);
	}
	for(int i = 0; i < int(log2(M.size())); i++){
		r1.push_back(r[i+int(log2(M[0].size()))]);
	}
	clock_t start,end;
	start = clock();
	
	vector<F> arr = prepare_matrix((transpose(M)),r1);
	
	vector<F> Fg1(M[0].size()); 
	phiGInit(Fg1,r2.begin(),F(1),r2.size(),false);
	struct proof Pr = generate_2product_sumcheck_proof(Fg1,arr,r[r.size()-1]);
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
	
	if(previous_sum != Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1)){
		printf("Error in fft\n");
		exit(-1);
	}
	Pr.randomness.push_back(r1); 
	Pr.randomness.push_back(r2);
	Pr.type = MATMUL_PROOF;
	return Pr;
}

struct proof _prove_matrix2vector(vector<vector<F>> M, vector<F> v, vector<F> r, F previous_sum){
	struct proof Pr;
	
	

	
	auto ts = high_resolution_clock::now();
	
	vector<F> V = prepare_matrix(M,r);
	
	//printf("(%d,%d),(%d,%d),(%d,%d)\n",M1.size(),M1[0].size(),M2.size(),M2[0].size(),V[0].size(),V[1].size());
	if(V.size() != 1){
		Pr = generate_2product_sumcheck_proof(V,v,r[r.size()-1]);
		Pr.randomness.push_back(r);
		
		if(previous_sum != (Pr.q_poly[0].eval(0) +Pr.q_poly[0].eval(1)) ){
			printf("Error in Matrix2vector multiplication\n");
			//exit(-1);
		}
		Pr.type = MATMUL_PROOF;
	}
	auto te = high_resolution_clock::now();
	auto tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;

	return Pr;
}



struct proof _prove_matrix2matrix_transpose(vector<vector<F>> &M1, vector<F> r, F previous_sum){
	struct proof Pr;
	clock_t start,end;
	start = clock();
	printf("%d\n",r.size() );
	vector<F> V1 = prepare_matrix(transpose(M1),r);
	
	vector<F> V2 = V1;
	printf("%d\n",V1.size() );
	//vector<vector<F>> V = prepare_matrixes(M1,M2,r1,r2);
	
	//printf("(%d,%d),(%d,%d),(%d,%d)\n",M1.size(),M1[0].size(),M2.size(),M2[0].size(),V[0].size(),V[1].size());
	
	Pr = generate_2product_sumcheck_proof(V1,V2,r[r.size()-1]);
	Pr.randomness.push_back(r);
	if(previous_sum != (Pr.q_poly[0].eval(0) +Pr.q_poly[0].eval(1)) ){
		printf("Error in Matrix2Matrix multiplication\n");
		exit(-1);
		//printf("Sumcheck Ok, %d\n", V[0].size());
	}
	Pr.type = MATMUL_PROOF;
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
	return Pr;
}

struct proof _prove_matrix2matrix(vector<vector<F>> M1, vector<vector<F>> M2, vector<F> r, F previous_sum){
	struct proof Pr;
	vector<F> r1(int(log2(M1.size()))); 
	vector<F> r2(int(log2(M2.size())));
	for(int i = 0; i < r2.size(); i++){
		r2[i] = (r[i]);
	}
	for(int i = 0; i < r1.size(); i++){
		r1[i] = (r[i+r2.size()]);
	}
	
	auto ts = high_resolution_clock::now();
	
	
	vector<vector<F>> V = prepare_matrixes(M1,M2,r1,r2);
	

	//printf("(%d,%d),(%d,%d),(%d,%d)\n",M1.size(),M1[0].size(),M2.size(),M2[0].size(),V[0].size(),V[1].size());
	if(V[0].size() != 1){
		Pr = generate_2product_sumcheck_proof(V[0],V[1],r[r.size()-1]);
		Pr.randomness.push_back(r1);
		Pr.randomness.push_back(r2);
		
		if(previous_sum != (Pr.q_poly[0].eval(0) +Pr.q_poly[0].eval(1)) ){
			//printf("Error in Matrix2Matrix multiplication\n");
			//exit(-1);
			//printf("Sumcheck Ok, %d\n", V[0].size());
		}
		Pr.type = MATMUL_PROOF;
	}else{
		
		Pr.randomness.push_back(r1);
		Pr.randomness.push_back(r2);
		if(previous_sum != V[0][0]*V[1][0]){
			printf("Error in Matrix2Matrix multiplication\n");
			exit(-1);
		}
		Pr.type = -1;
	}
	auto te = high_resolution_clock::now();
	auto tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;

	return Pr;
}



struct proof prove_matrix2matrix(vector<vector<F>> M1, vector<vector<F>> M2){
	
	vector<F> r1 = generate_randomness(int(log2(M1.size())),F(0));
	vector<F> r2 = generate_randomness(int(log2(M2.size())),F(0));
	
	vector<vector<F>> V = prepare_matrixes(M1,M2,r1,r2);
	struct proof Pr = generate_2product_sumcheck_proof(V[0],V[1],r2[r2.size()-1]);
	Pr.randomness.push_back(r1);
	Pr.randomness.push_back(r2);
	F sum = F(0);
	for(int i = 0; i < V[0].size(); i++){
		sum += V[0][i]*V[1][i];
	}
	if(sum == (Pr.q_poly[0].eval(0) +Pr.q_poly[0].eval(1)) ){
		//printf("Sumcheck Ok, %d\n", V[0].size());
	}
	Pr.type = MATMUL_PROOF;
	return Pr;
}

vector<vector<F>> generate_bit_matrix(vector<F> bits,int domain){
	vector<vector<F>> M;
	int elements = bits.size()/domain; 
	M.resize(domain);
	for(int i = 0; i < M.size(); i++){
		for(int j = 0; j < elements; j++){
			M[i].push_back(bits[j*domain+i]);
		}
	}
	return M;
}

void check_integrity(vector<F> bits, vector<F> num, vector<F> powers){
	for(int i = 0; i < bits.size()/256; i++){
		F sum = F(0);
		for(int j = 0; j  < 256; j++){
			sum += powers[j]*bits[i*256 + j];
		}
		
		char buff[257];
		/*
		sum.getStr(buff,257,2);
		printf("%s\n",buff);
		num[i].getStr(buff,257,2);
		printf("%s\n",buff );
		*/
		(num[i]-sum).getStr(buff,257,2);
		printf("%s\n",buff );
		
		if(bits[i*256+253] != 0){
			printf("Error ^2\n");
		}
		if(sum != num[i]){
			printf("Error\n");
		}
	}
}

F single_sum(vector<F> &v,vector<F> &beta){
	F sum = F(0);
	
	for(int i = 0; i < v.size(); i++){
		if(v[i] != F(0)){
			sum = sum+beta[i];
		}
	}
	return sum;
}

void _single_sum(vector<F> &individual_sums, vector<vector<F>> &partitions, vector<F> &beta, int idx, int K){
	
	if(threads < K){
		for(int i = idx; i < K; i += threads){
			individual_sums[i] = single_sum(partitions[i],beta);
		}
	}else{
		if(idx < K){
			
			individual_sums[idx] = single_sum(partitions[idx],beta);		
		}

	}
}

F double_sum(vector<F> &v1, vector<F> &v2,vector<F> &beta){
	F sum= F(0);
	
	for(int i = 0; i < v1.size(); i++){
		if(v1[i] == F(1) && v2[i] == F(1)){
			sum = sum+beta[i];
		}
	}
	return sum;
}


void _double_sum(vector<vector<F>> &Partial_sums, vector<vector<F>> &partitions,vector<F> &beta, int idx, int K){
	vector<vector<int>> pos(K*(K-1)/2);
	int counter = 0;
	
	for(int i = 0; i < K; i++){
		for(int j = i+1; j < K; j++){
			pos[counter].push_back(i);
			pos[counter].push_back(j);
			counter++;
		}
	}
	for(int i = idx; i < K*(K-1)/2; i += threads){
		Partial_sums[pos[i][0]][pos[i][1] - pos[i][0]-1] = double_sum(partitions[pos[i][0]],partitions[pos[i][1]],beta);
	}
}

vector<F> compute_all_sums(vector<F> r){
	int size = 1<<r.size();
	vector<F> sums(size,F(0));
	for(int i = 0; i < r.size(); i++){
		vector<F> temp(1<<i);
		for(int j = 0; j < temp.size(); j++){
			temp[j] = sums[j];
		}
		
		for(int j = 0; j < temp.size(); j++){
			sums[j<<1] = temp[j];
			sums[(j<<1)+1] = temp[j] + r[r.size()-i-1];
		}
	}
	return sums;
}

void _fold_bits(vector<vector<F>> &partitions, vector<F> &sums, vector<F> &folded_bits, int idx){
	int size = folded_bits.size()/threads;
	int pos = idx*(folded_bits.size()/threads);
	int num = 0; 
	for(int i = pos; i < pos + size; i++){
		num = 0;
		for(int j = 0; j < partitions.size(); j++){
			if(partitions[j][i] == F(1)){
				num += (1<<j); 
			}
		}

		folded_bits[i] = (sums[num]);
	}
}

vector<F> fold_bits(vector<vector<F>> &partitions, vector<F> &sums){
	vector<F> folded_bits(partitions[0].size());
	int num = 0;
	if(threads == 1){
		for(int i = 0; i < partitions[0].size(); i++){
			num = 0;
			for(int j = 0; j < partitions.size(); j++){
				if(partitions[j][i] == F(1)){
					num += (1<<j); 
				}
			}

			folded_bits[i] = (sums[num]);
		}
	}else{
		thread workers[threads];
		for(int i = 0; i < threads; i++){
			workers[i] = thread(&_fold_bits,ref(partitions),ref(sums),ref(folded_bits),i);
		}
		for(int i = 0; i < threads; i++){
			workers[i].join();
		}
	}
	return folded_bits;
}


void _predicate_sumcheck_phase1(F *v1,vector<F> &_v1,F *v2, vector<F> &_v2,F *v3, vector<F> &_v3,
 									F *v4, vector<F> &_v4, F *new_v1,F *new_v2,F *new_v3,F *new_v4  ,cubic_poly &poly, F rand, int idx, int L, int i){
	int size = L/threads;
	int pos = size*idx;
	cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
	linear_poly l1,l2,l3,l4;

	//printf("%d,%d,%d,%d,%d,%d,%d,%d,%d\n",L,threads,pos,pos+size,idx,_v1.size(),_v2.size(),_v3.size(),_v4.size() );
	for(int j = pos; j < pos+size; j++){
		
		if(i == 0){
			l1 = linear_poly(_v1[2*j+1] - _v1[2*j],_v1[2*j]);
			l2 = linear_poly(_v2[2*j+1] - _v2[2*j],_v2[2*j]);
			l3 = linear_poly(_v3[2*j+1] - _v3[2*j],_v3[2*j]);
			l4 = linear_poly(_v4[2*j+1] - _v4[2*j],_v4[2*j]);
		}else{
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
			l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
			l4 = linear_poly(v4[2*j+1] - v4[2*j],v4[2*j]);		
		}
		temp_poly = (l2-l4*l3)*l1;
		poly = poly + temp_poly;

		
		if(i == 0){
			new_v1[j] = _v1[2*j] + rand*(_v1[2*j+1] - _v1[2*j]);
			new_v2[j] = _v2[2*j] + rand*(_v2[2*j+1] - _v2[2*j]);
			new_v3[j] = _v3[2*j] + rand*(_v3[2*j+1] - _v3[2*j]);
			new_v4[j] = _v4[2*j] + rand*(_v4[2*j+1] - _v4[2*j]);
			
		}else{
			new_v1[j] = v1[2*j] + rand*(v1[2*j+1] - v1[2*j]);
			new_v2[j] = v2[2*j] + rand*(v2[2*j+1] - v2[2*j]);
			new_v3[j] = v3[2*j] + rand*(v3[2*j+1] - v3[2*j]);
			new_v4[j] = v4[2*j] + rand*(v4[2*j+1] - v4[2*j]);
		}
	}
} 


struct proof predicate_sumcheck_phase1(vector<F> &_v1, vector<F> &_v2, vector<F> &_v3, vector<F> &_v4){
	struct proof Pr;
	vector<F> r = generate_randomness(int(log2(_v1.size())),F(0));
	vector<cubic_poly> p;
	
	F *v1 = (F *)malloc(_v1.size()*sizeof(F)/2);
	F *v2 = (F *)malloc(_v2.size()*sizeof(F)/2);
	F *v3 = (F *)malloc(_v3.size()*sizeof(F)/2);
	F *v4 = (F *)malloc(_v4.size()*sizeof(F)/2);
	
	for(int i = 0; i < r.size(); i++){

		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		int L = 1 << (r.size() -1- i);
		if(threads == 1 || L <= 1<<10){

			cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3,l4;
			
			for(int j = 0; j < L; j++){
					if(i == 0){
						l1 = linear_poly(_v1[2*j+1] - _v1[2*j],_v1[2*j]);
						l2 = linear_poly(_v2[2*j+1] - _v2[2*j],_v2[2*j]);
						l3 = linear_poly(_v3[2*j+1] - _v3[2*j],_v3[2*j]);
						l4 = linear_poly(_v4[2*j+1] - _v4[2*j],_v4[2*j]);
					}else{
						l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
						l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
						l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
						l4 = linear_poly(v4[2*j+1] - v4[2*j],v4[2*j]);		
					}
					temp_poly = (l2-l4*l3)*l1;
					poly = poly + temp_poly;

				if(i == 0){
					v1[j] = _v1[2*j] + r[i]*(_v1[2*j+1] - _v1[2*j]);
					v2[j] = _v2[2*j] + r[i]*(_v2[2*j+1] - _v2[2*j]);
					v3[j] = _v3[2*j] + r[i]*(_v3[2*j+1] - _v3[2*j]);
					v4[j] = _v4[2*j] + r[i]*(_v4[2*j+1] - _v4[2*j]);
					
				}else{
					v1[j] = v1[2*j] + r[i]*(v1[2*j+1] - v1[2*j]);
					v2[j] = v2[2*j] + r[i]*(v2[2*j+1] - v2[2*j]);
					v3[j] = v3[2*j] + r[i]*(v3[2*j+1] - v3[2*j]);
					v4[j] = v4[2*j] + r[i]*(v4[2*j+1] - v4[2*j]);

				}
			}
			
		}else{
			vector<cubic_poly> _poly(threads);
			thread worker[threads];
			//vector<F> new_v1(L),new_v2(L);
			

			F *new_v1 = (F *)malloc(L*sizeof(F));
			F *new_v2 = (F *)malloc(L*sizeof(F));
			F *new_v3 = (F *)malloc(L*sizeof(F));
			F *new_v4 = (F *)malloc(L*sizeof(F));
			
			
			for(int j = 0; j < _poly.size(); j++){
				_poly[j] = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			}
			for(int j = 0; j < threads; j++){
				//worker[i](_generate_2product_sumcheck,ref(v1),ref(v2),ref(_poly[i]),rand,i,L);
				worker[j] = thread(&_predicate_sumcheck_phase1,(v1),ref(_v1),(v2),ref(_v2),(v3),ref(_v3),(v4),ref(_v4),new_v1,new_v2,new_v3,new_v4,ref(_poly[j]),r[i],j,L,i);
				//worker.push_back(move(th));
			}
			for(int j = 0; j < threads; j++){
				worker[j].join();
				poly = poly+ _poly[j];
			}
			
			v1 = new_v1;
			v2 = new_v2;
			v3 = new_v3;
			v4 = new_v4;
				
		}
		p.push_back(poly);

	}
	
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v3[0]);
	Pr.vr.push_back(v4[0]);
	
	return Pr;
}

F compute_beta(vector<F> r1, vector<F> r2){
	F prod = F(1);
	for(int i = 0; i < r1.size(); i++){
		prod = prod*((F(1)-r1[i])*(F(1)-r2[i]) + r1[i]*r2[i]);
	}
	return prod;
}

void _prepare_data(vector<F> &beta1,vector<F> &beta2,vector<F> &Hg1,vector<F> &Hg2,vector<int> &input, vector<F> &W, int idx){
	int size = Hg1.size()/threads;
	int pos = idx*size;
	for(int i = pos; i < pos+size; i++){
		Hg1[i] = beta2[input[i]]*W[input[i]];
		Hg2[i] = beta2[input[i]];
	}
}

void prepare_data(vector<F> &beta1,vector<F> &beta2,vector<F> &Hg1,vector<F> &Hg2,vector<int> &input, vector<F> W){
	if(threads > 1){
		thread workers[threads];
		for(int i = 0; i < threads; i++){
			workers[i] = thread(&_prepare_data,ref(beta1),ref(beta2),ref(Hg1),ref(Hg2),ref(input),ref(W),i);
		}
		for(int i = 0; i < threads; i++){
			workers[i].join();
		}

	}else{
		for(int i = 0; i < Hg1.size(); i++){
			Hg1[i] = beta2[input[i]]*W[input[i]];
			Hg2[i] = beta2[input[i]];
		}
	}
}

void lookup_range_proof(vector<int> input, int domain){
	vector<F> W,X;
	char buff[256];
	
	
	for(int i = 0; i < domain; i++){
		W.push_back(F(i));
	}
	for(int i = 0; i < input.size(); i++){
		X.push_back(F(input[i]));
	}
	int bit_size_input = (int)log2(input.size());
	vector<F> r_in,r_dom,r1,r2;
	r_in = generate_randomness(bit_size_input,F(0));
	r1 = generate_randomness(bit_size_input,F(0));
	r_dom = generate_randomness(Q,F(0));
	r2 = generate_randomness(Q,F(0));
	vector<F> Hg1((input).size()),Hg2(input.size());
	
	auto ts = high_resolution_clock::now();

	vector<F> beta1;
	precompute_beta(r_in,beta1);

	vector<F> beta2;
	precompute_beta(r_dom,beta2);
	
	
	prepare_data(beta1,beta2,Hg1,Hg2,input,W);
	

	
	struct proof P = predicate_sumcheck_phase1(beta1,Hg1,Hg2,X);
	

	range_proof_size += 4*P.c_poly.size()*sizeof(beta1[0]);

	if(P.c_poly[0].eval(0) + P.c_poly[0].eval(1) != F(0)){
		printf("Error\n");
		exit(-1);
	}

	
	r1 = P.randomness[0];
	F X_j = P.vr[3];
	F _b = P.vr[0];
	F Hg2_eval = P.vr[2];
	F last = P.c_poly[P.c_poly.size()-1].eval(P.randomness[0][P.randomness[0].size()-1]);
	

	
	vector<F> temp_beta;
	
	precompute_beta(P.randomness[0],temp_beta);


	vector<F> predicate(W.size(),F(0));
	
	for(int i = 0; i < X.size(); i++){
		predicate[input[i]] = predicate[input[i]] + temp_beta[i];
	}
	

	proof P1 = generate_2product_sumcheck_proof(predicate,beta2,r_dom[0]);
	range_proof_size += (3*P1.q_poly.size() + 3)*sizeof(beta1[0]);
	
	struct proof P2 = generate_3product_sumcheck_proof_naive(predicate,beta2,W, P1.randomness[0]);
	range_proof_size += (4*P2.c_poly.size()+4)*sizeof(beta1[0]);
	

	if(_b*(-X_j*(P1.q_poly[0].eval(0) + P1.q_poly[0].eval(1)) + (P2.c_poly[0].eval(0) + P2.c_poly[0].eval(1))) != last){
		printf("Error in 1st sumcheck\n");
		exit(-1);
	}


	vector<F> ones(predicate.size(),F(1));
	struct proof P3 = generate_2product_sumcheck_proof(predicate,ones,r_dom[0]);
	if(P3.q_poly[0].eval(1) + P3.q_poly[0].eval(0) != F(1)){
		printf("Error 2nd sumcheck\n");
		exit(-1);
	}
	range_proof_size += (3*P3.q_poly.size() + 3)*sizeof(beta1[0]);

	auto te = high_resolution_clock::now();
	auto tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;
	printf("%lf\n", tduration.count()/1000000.0);
	
	ts = high_resolution_clock::now();
	for(int i = 0; i < P.c_poly.size(); i++){
		F c = P.c_poly[i].eval(0) + P.c_poly[i].eval(1);
		c = P.c_poly[i].eval(P.randomness[0][i]);
	}
	for(int i = 0; i < P1.q_poly.size(); i++){
		F c = P1.q_poly[i].eval(0) + P1.q_poly[i].eval(1);
		c = P1.q_poly[i].eval(P1.randomness[0][i]);
	}
	
	for(int i = 0; i < P2.c_poly.size(); i++){
		F c = P2.c_poly[i].eval(0) + P2.c_poly[i].eval(1);
		c = P2.c_poly[i].eval(P2.randomness[0][i]);
	}
	
	for(int i = 0; i < P3.q_poly.size(); i++){
		F c = P3.q_poly[i].eval(0) + P3.q_poly[i].eval(1);
		c = P3.q_poly[i].eval(P3.randomness[0][i]);
	}

		
	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
	range_proof_verification_time += tduration.count()/1000000.0;

}



struct proof _prove_bit_decomposition_folded(vector<F> bits, vector<F> r1, F previous_sum, int domain){
	//int domain = 256;
	vector<F> powers;
	powers.push_back(F(1));
	for(int i = 1; i < domain; i++){
		powers.push_back(F(2)*powers[i-1]);
	}

	//check_integrity(bits,num,powers);


	vector<vector<F>> M = generate_bit_matrix(bits,domain);
	int K = 8;

	vector<vector<F>> partitions(K);
	vector<vector<F>> Partial_sums(K);
	vector<F> individual_sums(K);
	int counter = 0;
	for(int i = 0; i < K; i++){
		for(int j = 0; j < bits.size()/K; j++){
			partitions[i].push_back(bits[i*bits.size()/K + j]);
		}
	}
	
	auto s = high_resolution_clock::now();
	
	//vector<F> r1 = generate_randomness(int(log2(num.size())));
	auto ts = high_resolution_clock::now();
	
	vector<F> v1 = prepare_matrix((M),r1);
	auto te = high_resolution_clock::now();
	auto tduration = duration_cast<microseconds>(te - ts);
 	//printf("Matrix : %lf\n",tduration.count()/1000000.0);
	

	M.clear();
	struct proof Pr1 = generate_2product_sumcheck_proof(v1,powers,r1[r1.size()-1]);
	if(previous_sum != Pr1.q_poly[0].eval(0) + Pr1.q_poly[0].eval(1)){
		printf("Error in bit_decomposition\n");
		exit(-1);
	}
	
	
	
	vector<F> r2 = generate_randomness(int(log2(bits.size()/K)),r1[r1.size()-1]);
	
	ts = high_resolution_clock::now();
	vector<F> beta; 
	precompute_beta(r2,beta);
	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
 	//printf("Beta : %lf\n",tduration/1000000.0);
	
	


	
	ts = high_resolution_clock::now();

	if(threads == 1){
		for(int i = 0; i < K; i++){
			individual_sums[i] = single_sum(partitions[i],beta);
		}
		
		for(int i = 0; i < K; i++){
			for(int j = i+1; j < K; j++){
				Partial_sums[i].push_back(double_sum(partitions[i],partitions[j],beta));
				counter++;
			}
		}
	}else{
		thread workers[threads];
		ts = high_resolution_clock::now();
		
		for(int i = 0; i < threads; i++){
			workers[i] = thread(&_single_sum,ref(individual_sums),ref(partitions),ref(beta),i,K);
		}
		for(int i = 0; i < threads; i++){
			workers[i].join();
		}
		te = high_resolution_clock::now();
		tduration = duration_cast<microseconds>(te - ts);
 		//printf("Sums 1: %lf\n",tduration/1000000.0);
		ts = high_resolution_clock::now();
		
		for(int i = 0; i < K; i++){
			Partial_sums[i].resize(K - i - 1);
		}

		for(int i = 0; i < threads; i++){
			workers[i] = thread(&_double_sum,ref(Partial_sums),ref(partitions),ref(beta),i,K);			
		}
		for(int i = 0; i < threads; i++){
			workers[i].join();
		}
	}
	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
 	//printf("Sums : %lf\n",tduration/1000000.0);
	
	
	vector<F> r = generate_randomness(K,F(0));
	
	vector<F> sums = compute_all_sums(r);
	
	


	ts = high_resolution_clock::now();
	vector<F> folded_bits = fold_bits(partitions,sums);
	//for(int i = 0; i < folded_bits.size(); i++){
	//	nfolded_bits[i] = (sums[sums.size()-1] - folded_bits[i]);
	//}
	te = high_resolution_clock::now();
	vector<F> nfolded_bits(folded_bits.size());
	tduration = duration_cast<microseconds>(te - ts);
 	//printf("Fold time : %lf\n",tduration/1000000.0);
	
	ts = high_resolution_clock::now();
	struct proof Pr2 = generate_3product_sumcheck_proof_folded(beta,folded_bits,nfolded_bits,sums[sums.size()-1],r2[r2.size()-1]);
	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
 	//printf("Sumcheck : %lf\n",tduration/1000000.0);
	
	auto e = high_resolution_clock::now();
	auto duration = duration_cast<microseconds>(e - s);
 
	
	
	proving_time += duration.count()/1000000.0;
	
	F sum = F(0);
	for(int i = 0; i < K; i++){
		for(int j = i+1; j < K; j++){
			sum += F(2)*r[i]*r[j]*Partial_sums[i][j-i-1];
		}
	}
	sum = F(0) - sum;
	vector<F> mul(K,F(0));
	for(int i = 0; i < K; i++){
		for(int j = 0; j < K; j++){
			if(j != i){
				mul[i] = mul[i]+r[j];
			}
		}
	}
	for(int i = 0; i < K; i++){
		sum += mul[i]*individual_sums[i]*r[i];
	}
	//e = high_resolution_clock::now();
	
	//duration = duration_cast<microseconds>(e - s);
 
	//printf("Bit decomposition : %d, %f\n", bits.size(),duration/1000000.0);
	
	
	if(sum != Pr2.c_poly[0].eval(0) + Pr2.c_poly[0].eval(1)){
		printf("Error\n");
		exit(-1);
	}
	struct proof Pr;
	Pr.randomness.push_back(r1);
	Pr.randomness.push_back(r2);
	Pr.randomness.push_back(Pr1.randomness[0]);
	Pr.randomness.push_back(Pr2.randomness[0]);
	Pr.vr.insert(Pr.vr.end(),Pr1.vr.begin(),Pr1.vr.end());
	Pr.vr.insert(Pr.vr.end(),Pr2.vr.begin(),Pr2.vr.end());
	Pr.q_poly = Pr1.q_poly;
	Pr.c_poly = Pr2.c_poly;
	Pr.type = RANGE_PROOF_OPT;
	Pr.w_hashes.insert(Pr.w_hashes.end(),Pr1.w_hashes.begin(),Pr1.w_hashes.end());
	Pr.w_hashes.insert(Pr.w_hashes.end(),Pr2.w_hashes.begin(),Pr2.w_hashes.end());
	Pr.r = r;
	Pr.Partial_sums = Partial_sums;
	Pr.individual_sums = individual_sums;
	Pr.K = K;
	return Pr;

}


struct proof _prove_bit_decomposition(vector<F> bits, vector<F> r1, F previous_sum, int domain){
	//int domain = 256;
	vector<F> powers;
	powers.push_back(F(1));
	for(int i = 1; i < domain; i++){
		powers.push_back(F(2)*powers[i-1]);
	}

	//check_integrity(bits,num,powers);


	clock_t start,end;
			
	start = clock(); 
	vector<vector<F>> M = generate_bit_matrix(bits,domain);
	auto s = high_resolution_clock::now();
	
	auto st = high_resolution_clock::now();
	//vector<F> r1 = generate_randomness(int(log2(num.size())));
	vector<F> v1 = prepare_matrix((M),r1);
	auto se = high_resolution_clock::now();
	auto duration = duration_cast<microseconds>(se - st);
	//printf("Matrix : %f\n",duration.count()/1000000.0);
	
	M.clear();

	struct proof Pr1 = generate_2product_sumcheck_proof(v1,powers,r1[r1.size()-1]);
	if(previous_sum != Pr1.q_poly[0].eval(0) + Pr1.q_poly[0].eval(1)){
		printf("Error in bit_decomposition\n");
		exit(-1);
	}
	vector<F> r2 = generate_randomness(int(log2(bits.size())),r1[r1.size()-1]);
	vector<F> beta; 
	
	st = high_resolution_clock::now();
	precompute_beta(r2,beta);
	se = high_resolution_clock::now();
	duration = duration_cast<microseconds>(se - st);
	//printf("beta : %f\n",duration.count()/1000000.0);
	
	vector<F> inv_bits;
	
	st = high_resolution_clock::now();
	
	struct proof Pr2 = generate_3product_sumcheck_proof(beta,bits,inv_bits,r2[r2.size()-1]);
	se = high_resolution_clock::now();
	duration = duration_cast<microseconds>(se - st);
	//printf("sumcheck : %f\n",duration.count()/1000000.0);
	
	auto e = high_resolution_clock::now();
 
	// To get the value of duration use the count()
	// member function on the duration object
	
	duration = duration_cast<microseconds>(e - s);
	end = clock();
	proving_time += duration.count()/1000000.0;
	//printf("Bit decomposition : %d, %f\n", bits.size(),duration.count()/1000000.0);
	struct proof Pr;
	Pr.randomness.push_back(r1);
	Pr.randomness.push_back(r2);
	Pr.randomness.push_back(Pr1.randomness[0]);
	Pr.randomness.push_back(Pr2.randomness[0]);
	Pr.vr.insert(Pr.vr.end(),Pr1.vr.begin(),Pr1.vr.end());
	Pr.vr.insert(Pr.vr.end(),Pr2.vr.begin(),Pr2.vr.end());
	Pr.q_poly = Pr1.q_poly;
	Pr.c_poly = Pr2.c_poly;
	Pr.type = RANGE_PROOF;
	Pr.w_hashes.insert(Pr.w_hashes.end(),Pr1.w_hashes.begin(),Pr1.w_hashes.end());
	Pr.w_hashes.insert(Pr.w_hashes.end(),Pr2.w_hashes.begin(),Pr2.w_hashes.end());
	
	return Pr;

}


struct proof prove_bit_decomposition(vector<F> bits, vector<F> num, int domain){
	//int domain = 256;
	vector<F> powers;
	powers.push_back(F(1));
	for(int i = 1; i < domain; i++){
		powers.push_back(F(2)*powers[i-1]);
	}

	//check_integrity(bits,num,powers);


	clock_t start,end;
			
	start = clock(); 
	vector<vector<F>> M = generate_bit_matrix(bits,domain);
	vector<F> r1 = generate_randomness(int(log2(num.size())),F(0));
	vector<F> v1 = prepare_matrix((M),r1);
	
	struct proof Pr1 = generate_2product_sumcheck_proof(v1,powers,r1[r1.size()-1]);
	
	vector<F> r2 = generate_randomness(int(log2(bits.size())),F(0));
	vector<F> beta; 
	precompute_beta(r2,beta);
	
	vector<F> inv_bits;
	for(int i  = 0; i < bits.size(); i++){
		inv_bits.push_back(F(1) - bits[i]);
	}
	
	struct proof Pr2 = generate_3product_sumcheck_proof(beta,bits,inv_bits,r2[r2.size()-1]);
	
	end = clock();
	

	struct proof Pr;
	Pr.randomness.push_back(r1);
	Pr.randomness.push_back(r2);
	Pr.randomness.push_back(Pr1.randomness[0]);
	Pr.randomness.push_back(Pr2.randomness[0]);
	Pr.vr.insert(Pr.vr.end(),Pr1.vr.begin(),Pr1.vr.end());
	Pr.vr.insert(Pr.vr.end(),Pr2.vr.begin(),Pr2.vr.end());
	Pr.q_poly = Pr1.q_poly;
	Pr.c_poly = Pr2.c_poly;
	Pr.type = RANGE_PROOF;
	return Pr;

}


F inner_product(vector<F> v1, vector<F> v2){
	F sum = F(0);
	for(int i = 0; i < v1.size(); i++){
		sum += v1[i]*v2[i];
	}
	return sum;
}



struct proof gkr_proof(string circuit_filename,string data_filename, vector<F> data, vector<F> r, bool debug){
	char name[data_filename.length()+1];
	char circuit_name[circuit_filename.length()+1];
	strcpy(name, data_filename.c_str());
	strcpy(circuit_name, circuit_filename.c_str());
	//write_data(data,name);
	printf("%s\n",circuit_name );
	
	return generate_GKR_proof(circuit_name,name,data,r,debug);
	
}


vector<vector<F>> matrix2matrix(vector<vector<F>> M1,vector<vector<F>> M2){
	vector<vector<F>> M;
	
	M.resize(M1.size());
	for(int i = 0; i < M1.size(); i++){
		M[i].resize(M2.size());
	}
	for(int i = 0; i< M1.size(); i++){
		for(int j = 0; j < M2.size(); j++){
			//printf("%d,%d,%d,%d \n",i,j, M1.size(), M2.size() );
			M[i][j] = (inner_product(M1[i],M2[j]));
		}
	}
	
	return M;
}



struct _temp generate_vector(){
	//vector<int> v;
	struct _temp e;
	for(int i = 0; i < 10; i++){
		e.v.push_back(i);
	}
	return e;

}


vector<vector<vector<F>>> generate_matrix(){
	int m,n,l;
	m = 8;
	n = 16;
	l = 4;
	vector<vector<F>> M1;
	vector<vector<F>> M2;
	vector<vector<vector<F>>> M;
	
	for(int i = 0; i < m; i++){
		M1.push_back(generate_randomness(l,F(0)));
	}
	for(int i = 0; i < n; i++){
		M2.push_back(generate_randomness(l,F(0)));
	}
	M.push_back(M1);
	M.push_back(M2);
	return M;
}

vector<F> negate_bits(vector<F> bits){
	char buff[257];
	vector<F> nbits;
	F num;
	for(int i = 0; i < bits.size(); i++){
		bits[i].getStr(buff,257,2);
		if(buff[0] == '1'){
			num = F(0);
			nbits.push_back(num);
		}
		else if(buff[0] == '0'){
			num = F(1);
			nbits.push_back(num);
		}
		else{
			printf("Error in negating bits. Aborting\n");
			exit(-1);
		}
	}
	return nbits;
}

F compute_sum_v1v1(vector<F> &v,vector<F> &b, vector<int> &idx ,vector<F> &vals){
	vector<F> Partial_sums(vals.size(),F(0));
	F sum = F(0);
	F sum2 = F(0);
	for(int i = 0; i < b.size(); i++){
		if(idx[i] != 0){
			Partial_sums[idx[i]] += b[i];
		}
	}

	for(int i = 0; i < Partial_sums.size(); i++){
		sum += Partial_sums[i]*Partial_sums[i]*vals[i];
		sum2 += Partial_sums[i]*vals[i];
	}
	return sum;
}

F compute_sum_v1(vector<F> &v,vector<F> &b, vector<int> &idx ,vector<F> &vals){
	vector<F> Partial_sums(vals.size(),F(0));
	F sum = F(0);

	for(int i = 0; i < b.size(); i++){
		if(idx[i] != 0){
			Partial_sums[idx[i]] += b[i];
		}
	}
	for(int i = 0; i < Partial_sums.size(); i++){
		sum += Partial_sums[i]*vals[i];
	}
	return sum;
}

F compute_sum_v1v2(vector<F> &v1,vector<F> &v2,vector<F> &b1,vector<F> &b2, vector<int> &idx ,vector<F> &vals){
	vector<F> Partial_sums1(vals.size(),F(0));
	vector<F> Partial_sums2(vals.size(),F(0));
	
	F sum = F(0);
	F sum2 = F(0);
	for(int i = 0; i < b1.size(); i++){
		if(v2[i] != F(0)){
			Partial_sums1[idx[i]] += b1[i];
			Partial_sums2[idx[i]] += b2[i];
		}
	}
	for(int i = 0; i < Partial_sums1.size(); i++){
		sum += Partial_sums1[i]*vals[i];
		sum2 += Partial_sums2[i]*vals[i];
	}
	sum = F(2)*sum;
	return sum;	
}
F compute_sum_v2v2(vector<F> &v2,vector<F> &b1){
	
	F sum = F(0);

	for(int i = 0; i < b1.size(); i++){
		if(v2[i] != F(0)){
			sum += b1[i];
		}
	}
	return sum;	
}



void update_values(vector<F> &vals, unordered_map<F,int> &map, F num){
	int size = vals.size();
	
	for(int i = 0; i < size; i++){
		vals.push_back(vals[i] + num);
		map[vals[i] + num] = i+size;
	}

}

void update_idx(vector<vector<int>> &idx,unordered_map<F,int> &map, vector<vector<F>> &vals){
	for(int i = 0; i < vals.size(); i++){
		for(int j = 0; j < vals[i].size(); j++){
			idx[i][j] = map[vals[i][j]];
		}
	}
}

void fold(vector<vector<F>> &folded_vector, vector<vector<F>> &new_vector, vector<F> beta, vector<vector<int>> &idx, vector<F> &vals, unordered_map<F,int> &map){
	vector<F> new_beta;
	vector<F> r = generate_randomness((int)log2(folded_vector[0].size()),F(0));
	
	clock_t s,e;
	s = clock();

	precompute_beta(r,new_beta);
	vector<F> sums_v1v1,sums_v1v2,sums_v2v2,sums_v1;
	for(int i = 0; i < folded_vector.size(); i++){
		sums_v1v1.push_back(compute_sum_v1v1(folded_vector[i],new_beta,idx[i],vals));
	} 
	for(int i = 0; i < folded_vector.size(); i++){
		sums_v1v2.push_back(compute_sum_v1v2(folded_vector[i],new_vector[i],beta,new_beta,idx[i],vals));
	}
	
	for(int i = 0; i < folded_vector.size(); i++){
		sums_v2v2.push_back(compute_sum_v2v2(new_vector[i],beta));
	}
	F a;
	a.setByCSPRNG();
	for(int i = 0; i < beta.size(); i++){
		beta[i] += a*new_beta[i];
	}
	for(int i = 0; i < folded_vector.size(); i++){
		for(int j = 0; j < folded_vector[i].size(); j++){
			if(new_vector[i][j] != F(0)){
				folded_vector[i][j] += a;
			}
		}
	}
	e = clock();
	printf("%f\n",(float)(e-s)/(float)CLOCKS_PER_SEC);

	update_values(vals,map,a);

	update_idx(idx,map,folded_vector);

}

void fold_range_proof(int size){
	
	vector<vector<F>> folded_vector(8);
	vector<vector<int>> idx(8);
	for(int i = 0; i < folded_vector.size(); i++){
		folded_vector[i].resize(size);
		idx[i].resize(size);
		for(int j = 0; j < size; j++){
			folded_vector[i][j] = F(rand()%2);
		}
	}
	vector<F> vals;
	vals.push_back(F(0));
	vals.push_back(F(1));
	
	unordered_map<F,int> map;
	
	map[F(0)] = 0;
	map[F(1)] = 1;
	update_idx(idx,map,folded_vector);

	vector<F> beta;
	vector<F> r = generate_randomness((int)log2(size),F(0));
	precompute_beta(r,beta);

	for(int i = 0; i < 20; i++){
		vector<vector<F>> new_vector(8);
		for(int j = 0; j < 8; j++){
			new_vector[j].resize(size);
			for(int k = 0; k < size; k++){
				new_vector[j][k] = F(rand()%2);
			}
		} 
		fold(folded_vector,new_vector,beta,idx,vals,map);
	}	
	

}

void Range_proof(vector<F> input,vector<F> r, F previous_sum){
	vector<F> previous,beta;
	F num;

	
	//fold(previous,beta,num,prepare_bit_vector(input,Q));
	_prove_bit_decomposition_folded( prepare_bit_vector(input,Q),r,previous_sum,Q);
	_prove_bit_decomposition(prepare_bit_vector(input,Q),r, previous_sum, Q);
}

vector<proof> FoolsGold_Prove(int N, int M, FoolsGold &data){
	struct proof P;
	vector<proof> Proof;
	vector<F> gkr_input;
	vector<F> arr;
	vector<F> nbits;
	vector<vector<F>> mul_vector;
	vector<vector<F>> bit_matrix(N);
	

	mul_vector.resize(1);
	mul_vector[0].resize(256);
	for(int i = 0; i < mul_vector[0].size(); i++){
		mul_vector[0][i] = F(0);
	}
	mul_vector[0][254] = F(1);
	

	for(int i = 0; i < N; i++){
		bit_matrix[i].resize(256);
		for(int j = 0; j < 256; j++){
			bit_matrix[i][j] = data.inv_relu_bits[i*256+j];
		}
	}

	
	vector<F> r = generate_randomness((int)log2(M),F(0));
	
	F eval1 = evaluate_vector(data.aggr,r);
	P = _prove_matrix2vector(data.G,data.weights,r,eval1);
	Proof.push_back(P);

	r = P.randomness[0];
	// Prove inverse relu
	eval1 = P.vr[1];
	
	gkr_input = data.weights;
	for(int i = 0; i <  data.inv_most_significant_bits.size(); i++){
		arr.push_back(F(1) - data.inv_most_significant_bits[i]);
	}
	gkr_input.insert(gkr_input.end(),arr.begin(),arr.end());
	arr.clear();
	for(int i = 0; i < data.inv_most_significant_bits.size(); i++){
		arr.push_back(F(1<<Q)*data.inv_most_significant_bits[i]);
	}
	gkr_input.insert(gkr_input.end(),arr.begin(),arr.end());
	arr.clear();
	P = prove_inv_relu(gkr_input,r,N);
	Proof.push_back(P);

	if(eval1 != P.q_poly[0].eval(0) + P.q_poly[0].eval(1)){
		printf("Error in inv Relu\n");
		exit(-1);
	}
	r.clear();
	for(int i = 0; i < (int)log2(N); i++){
		r.push_back(P.randomness[P.randomness.size()-1][i]);
	}
	eval1 = evaluate_vector(data.output,r);
	
	P = _prove_bit_decomposition_folded(data.inv_relu_bits,r,F(1<<Q)-eval1,256);
	Proof.push_back(P);
	P = _prove_matrix2matrix(bit_matrix,mul_vector,r,evaluate_vector(data.inv_most_significant_bits,r));
	Proof.push_back(P);
	// Prove relu
	for(int i = 0; i < data.most_significant_bits.size(); i++){
		nbits.push_back(F(1) - data.most_significant_bits[i]);
	}
	gkr_input.clear();
	gkr_input.insert(gkr_input.end(),nbits.begin(),nbits.end());
	gkr_input.insert(gkr_input.end(),data.logit.begin(),data.logit.end());
	
	P = prove_relu(gkr_input,r,nbits.size());
	Proof.push_back(P);
	if(eval1 != P.q_poly[0].eval(0)+P.q_poly[0].eval(1)){
		printf("Error in Relu\n");
		exit(-1);
	}


	r.clear();
	for(int i = 0; i < (int)log2(N); i++){
		r.push_back(P.randomness[P.randomness.size()-1][i]);
	}
	F eval3 = evaluate_vector(data.logit,r);

	for(int i = 0; i < N; i++){
		for(int j = 0; j < 256; j++){
			bit_matrix[i][j] = data.relu_bits[i*256+j];
		}
	}
	P = _prove_bit_decomposition_folded(data.relu_bits,r,eval3,256);
	Proof.push_back(P);
	P = _prove_matrix2matrix(bit_matrix,mul_vector,r,evaluate_vector(data.most_significant_bits,r));
	Proof.push_back(P);


	arr = data.log_left;
	arr.insert(arr.end(),data.log_right.begin(),data.log_right.end());
	
	auto ts = high_resolution_clock::now();

	eval1 = evaluate_vector(data.log_left,r);
	F eval2 = evaluate_vector(data.log_right,r);
	auto te = high_resolution_clock::now();
	auto tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;
	if(eval3 != eval1 - eval2){
		printf("Error in Logit\n");
		exit(-1);
	}
	F rand;
	rand.setByCSPRNG();
	r.push_back(rand);
	eval3 = evaluate_vector(arr,r);
	arr.clear();
	
	gkr_input.clear();
	//gkr_input.insert(gkr_input.end(),data.normalized_values.begin(),data.normalized_values.end());
	for(int i = 0; i < N; i++){
		gkr_input.push_back(data.normalized_values[i] - F(1<<Q));
	}
	for(int i = 0; i < N; i++){
		gkr_input.push_back(F(1<<Q) - data.normalized_values[i] - F(1<<Q));
	}
	//gkr_input.insert(gkr_input.end(), arr.begin(),arr.end());
	gkr_input.insert(gkr_input.end(), data.log_input_1.begin(),data.log_input_1.end());
	gkr_input.insert(gkr_input.end(), data.log_input_2.begin(),data.log_input_2.end());

	P = prove_log(gkr_input,r,N);
	Proof.push_back(P);
	if(eval1*(1- r[r.size()-1]) + eval2*r[r.size()-1] != (P.q_poly[0].eval(0) + P.q_poly[0].eval(1))){
		printf("Error in Log\n");
		exit(-1);
	}	
	gkr_input.clear();
	r.clear();
	for(int i = 0; i < (int)log2(N); i++){
		r.push_back(P.randomness[P.randomness.size()-1][i]);
	}
	ts = high_resolution_clock::now();

	eval1 = evaluate_vector(data.normalized_values,r);
	eval2 = evaluate_vector(data.normalized_values_remainders,r);
	eval3 = evaluate_vector(data.shifted_max,r);
	
	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;
	
	if(F(1<<Q)*(F(1<<Q) - eval3) != data.max_val*eval1 + eval2){
		printf("Error in max3 division check\n");
	}
	P = _prove_bit_decomposition(data.normalized_bits,r,eval2,Q);
	Proof.push_back(P);
	gkr_input = data.max_3_difference;
	

	P = check_max(gkr_input,r,N,1);
	Proof.push_back(P);
	if(P.q_poly[0].eval(0) + P.q_poly[0].eval(1) != 0){
		printf("Error in check max\n");
		exit(-1);
	}
	r.clear();
	for(int i = 0; i < (int)log2(N); i++){
		r.push_back(P.randomness[P.randomness.size()-1][i]);
	}
	eval1 = evaluate_vector(data.max_3_difference,r);
	P = _prove_bit_decomposition(data.max_3_bits,r,eval1,Q);
	Proof.push_back(P);
	ts = high_resolution_clock::now();

	eval2 = evaluate_vector(data.shifted_max_remainders,r);
	eval3 = evaluate_vector(data.max_2,r);

	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;
	if( eval3 != F(1<<Q)*(eval1 - data.max_val + F(1<<Q)) + eval2){
		printf("Error in max shift\n");
		exit(-1);
	}
	P = _prove_bit_decomposition(data.shift_bits,r,eval2,Q);
	Proof.push_back(P);
	//r = generate_randomness((int)log2(data.max_2_difference.size()),F(0));
	vector<F> r2 = generate_randomness((int)log2(data.max_2_difference.size()),F(0));

	for(int i = (int)log2(data.max_2_difference.size()) - (int)log2(N); i < r2.size(); i++){
		r2[i] = r[i-((int)log2(data.max_2_difference.size()) - (int)log2(N))];
	}
	r = r2;
	ts = high_resolution_clock::now();

	eval1 = evaluate_vector(data.max_2_difference,r);
	eval2 = evaluate_vector(convert2vector(data.new_CS),r);
	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;
	//eval3 = evaluate_vector(data.max_2,r);
	if(eval1 != eval3 - eval2){
		printf("Error in max2\n");
		exit(-1);
	}


	P = _prove_bit_decomposition(data.max_2_bits,r,eval1,2*Q);
	Proof.push_back(P);
	gkr_input.clear();
	arr = convert2vector(data.CS); 
	gkr_input.insert(gkr_input.end(),arr.begin(),arr.end());
	gkr_input.insert(gkr_input.end(),data.pardon_div.begin(),data.pardon_div.end());
	P = hadamard_product(gkr_input,r,arr.size());
	Proof.push_back(P);
	if(P.q_poly[0].eval(0) + P.q_poly[0].eval(1) != eval2){
		printf("Error\n");
		exit(-1);
	}
	r.clear();
	for(int i = 0; i < (int)log2(arr.size()); i++){
		r.push_back(P.randomness[P.randomness.size()-1][i]);
	}
	
	gkr_input.clear();
	gkr_input.insert(gkr_input.end(),data.max_2_difference.begin(),data.max_2_difference.end());
	P = check_max(gkr_input,r,N,N);
	Proof.push_back(P);
	if(P.q_poly[0].eval(0) + P.q_poly[0].eval(1) != 0){
		printf("Error in max check 2\n");
		exit(-1);
	}
	//eval1 = evaluate_vector(arr,r);

	ts = high_resolution_clock::now();

	eval1 = evaluate_vector(data.pardon_remainders,r);

	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;

	P = _prove_bit_decomposition_folded(data.pardon_bits,r,eval1,Q);
	Proof.push_back(P);
	gkr_input.clear();
	gkr_input.insert(gkr_input.end(),data.max_1.begin(),data.max_1.end());
	arr.clear();
	for(int i = 0; i < data.max_1.size(); i++){
		arr.push_back((1<<Q)*data.max_1[i]);
	}
	gkr_input.insert(gkr_input.end(),arr.begin(),arr.end());
	gkr_input.insert(gkr_input.end(),data.pardon_div.begin(),data.pardon_div.end());
	gkr_input.push_back(F(0));
	P = pardon_div(gkr_input,r,N,N*N);
	Proof.push_back(P);
	if(P.q_poly[0].eval(1) + P.q_poly[0].eval(0) != eval1){
		printf("Error in Pardon Remainder computation\n");
		exit(-1);
	}

	r.clear();
	for(int i = 0; i < (int)log2(data.CS.size()*data.CS[0].size()); i++){
		r.push_back(P.randomness[P.randomness.size()-1][i]);
	}
	// Final phase
	ts = high_resolution_clock::now();

	eval1 = evaluate_vector(data.max_1_difference,r);
	eval2 = evaluate_vector(convert2vector(data.CS),r);

	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;
	
	eval3 = evaluate_vector(data.max_1,r);
	if(eval1 != eval3 - eval2){
		//printf("Error in max1\n");
		//exit(-1);
	}
	P = _prove_bit_decomposition(data.max_1_bits,r,eval1,Q);
	Proof.push_back(P);
	gkr_input.clear();
	gkr_input.insert(gkr_input.end(),data.max_1_difference.begin(),data.max_1_difference.end());

	P = check_max(gkr_input,r,N,N);
	Proof.push_back(P);
	// compute the dot product of CS and Sqrt_Matrix
	ts = high_resolution_clock::now();

	arr.clear();
	for(int i = 0; i < data.CS.size(); i++){
		for(int j = 0; j < data.CS[0].size(); j++){
			arr.push_back(data.CS[i][j]*data.sqrt_matrix[i][j]);
		}
	}
	r = generate_randomness((int)log2(data.CS.size()*data.CS[0].size()),F(0));
	
	eval1 = evaluate_vector(arr,r);
	eval2 = evaluate_vector(data.CS_remainders,r);
	eval3 = evaluate_vector(convert2vector(data.CS_temp),r);
	
	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;

	F final_eval = eval3;
	vector<F> final_r = r;
	if(eval1 + eval2 != (1<<Q)*eval3){
		printf("Error in division temp_QS/sqrt\n");
		exit(-1);
	}
	P = _prove_bit_decomposition_folded(data.CS_remainders_bits,r,eval2,4*Q);
	Proof.push_back(P);
	gkr_input.clear();
	arr = convert2vector(data.CS);
	gkr_input.insert(gkr_input.end(),arr.begin(),arr.end());
	arr = convert2vector(data.sqrt_matrix);
	gkr_input.insert(gkr_input.end(),arr.begin(),arr.end());
	
	P = hadamard_product(gkr_input,r,arr.size());
	Proof.push_back(P);
	if(P.q_poly[0].eval(0) + P.q_poly[0].eval(1) != eval1){
		printf("Error in hadamard product phase 1\n");
		exit(-1);
	}
	r.clear();
	for(int i = 0; i < (int)log2(N*N); i++){
		r.push_back(P.randomness[P.randomness.size()-1][i]);
	}

	ts = high_resolution_clock::now();
	
	eval1 = evaluate_vector(convert2vector(data.CS_temp),r);
	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;
	eval2 = evaluate_vector(convert2vector(data.sqrt_matrix),r);
	
	P = sqrt_matrix(data.sqrt,r,N);
	Proof.push_back(P);
	if(P.q_poly[0].eval(0) + P.q_poly[0].eval(1) != eval2){
		printf("Error in sqrt computation\n");
		exit(-1);
	}

	r.clear();
	r = generate_randomness((int)log2(N),F(0));

	ts = high_resolution_clock::now();

	eval1 = evaluate_vector(data.identity_elements,r);
	eval2 = evaluate_vector(data.sqrt_left,r);
	eval3 = evaluate_vector(data.sqrt_right,r);
	
	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;

	P = _prove_bit_decomposition(data.sqrt_left_bits,r,eval1 - eval2,2*Q);
	Proof.push_back(P);
	P = _prove_bit_decomposition(data.sqrt_right_bits,r,eval3 - eval1,2*Q);
	Proof.push_back(P);
	
	arr.clear();
	arr = convert2vector(data.CS_temp);
	arr.push_back(F(0));

	P = extract_diagonal(arr,r,N);
	Proof.push_back(P);
	if(P.q_poly[0].eval(0) + P.q_poly[0].eval(1) != eval1){
		printf("Error in extraction\n");
		exit(-1);
	}
	
	rand.setByCSPRNG();
	r.push_back(rand);

	arr.clear();
	arr = data.sqrt;
	arr.push_back(F(1));
	P = sqrt_aux(arr,r,N);
	if(eval3*(1-rand) + eval2*rand != P.q_poly[0].eval(0) + P.q_poly[0].eval(1)){
		printf("Error in sqrt aux generation\n");
		exit(-1);
	}
	
	P = _prove_matrix2matrix(data.G,data.G,final_r,final_eval);
	Proof.push_back(P);
	return Proof;
}


vector<proof> FLTrust_Prove(int N, int M, FLTrust data){
	vector<F> r;
	vector<F> gkr_data;
	vector<F> nbits;
	vector<proof> Proof;
	
	vector<vector<F>> bit_matrix;
	vector<vector<F>> mul_vector;
	mul_vector.resize(1);
	mul_vector[0].resize(256);
	for(int i = 0; i < mul_vector[0].size(); i++){
		mul_vector[0][i] = F(0);
	}
	mul_vector[0][254] = F(1);
	bit_matrix.resize(data.Prod.size());
	for(int i = 0; i < bit_matrix.size(); i++){
		bit_matrix[i].resize(256);
		for(int j = 0; j < 256; j++){
			bit_matrix[i][j] = data.relu_bits[i*256 + j];
		}
	}
	
	clock_t start,end;
	r = generate_randomness((int)log2(data.aggr.size()),F(0));
	F previous_sum = evaluate_vector(data.aggr,r);
	
	proof P = _prove_matrix2vector(data.G,data.output,r,previous_sum);
	Proof.push_back(P);
	for(int i = 0; i < data.most_significant_bits.size(); i++){
		nbits.push_back(F(1) - data.most_significant_bits[i]);
	}
	gkr_data.insert(gkr_data.end(),nbits.begin(),nbits.end());
	gkr_data.insert(gkr_data.end(),data.Prod.begin(),data.Prod.end());
	P = prove_relu(gkr_data,r,nbits.size());
	Proof.push_back(P);
	r.clear();
	for(int i = 0; i < (int)log2(data.Prod.size()); i++){
		r.push_back(P.randomness[P.randomness.size()-1][i]);
	}
	previous_sum = evaluate_vector(data.Prod,r);

	P = _prove_bit_decomposition_folded(data.relu_bits,r,previous_sum,256);
	Proof.push_back(P);
	P = _prove_matrix2matrix(bit_matrix,mul_vector,r,evaluate_vector(data.most_significant_bits,r));
	Proof.push_back(P);
	
	auto s = high_resolution_clock::now();
	F eval_n = evaluate_vector(data.Norms,r);
	F eval_q = evaluate_vector(data.quotients,r);
	F eval_r = evaluate_vector(data.remainders,r);
	
	auto e = high_resolution_clock::now();
	auto d = duration_cast<microseconds>(e - s);
	proving_time += d.count()/1000000.0;

	//proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
	

	if(eval_n != F(1<<Q)*eval_q + eval_r){
		printf("Error in Division\n");
		exit(-1);
	}
	P = _prove_bit_decomposition(data.remainder_bits,r,eval_r,Q);
	Proof.push_back(P);
	P = _prove_bit_decomposition(data.quotients_bits,r,F(1<<Q) - eval_q,Q);
	Proof.push_back(P);
	P =  _prove_matrix2matrix(data.G,data.tG,r,previous_sum);
	Proof.push_back(P);
	P = prove_norm(data.G,r,eval_n);
	Proof.push_back(P);
	printf("GKR prove time : %lf\n",proving_time );
	return Proof;
}

void FoolsGold_Commit(vector<MIPP_Comm> &commitments, FoolsGold data, int N, int M, int range_proof_method){
	commitments.resize(20);
	// N size :
	MIPP_gen((int)log2(N),commitments[0],false,false);
	copy_pp(commitments[0],commitments[1]);
	copy_pp(commitments[0],commitments[2]);
	copy_pp(commitments[0],commitments[3]);
	copy_pp(commitments[0],commitments[4]);
	copy_pp(commitments[0],commitments[5]);

	// N^2 size : 
	MIPP_gen(2*(int)log2(N),commitments[6],false,false);
	copy_pp(commitments[6],commitments[7]);
	
	// 4QN^2
	MIPP_gen(2+ (int)log2(Q) +2*(int)log2(N),commitments[8],false,true);
	
	// QN^2
	MIPP_gen((int)log2(Q) +2*(int)log2(N),commitments[9],false,true);
	
	// 256 N
	MIPP_gen((int)(8) +(int)log2(N),commitments[10],false,true);
	copy_pp(commitments[10],commitments[11]);
	// QN
	MIPP_gen((int)log2(Q) + (int)log2(N),commitments[12],false,true);
	copy_pp(commitments[12],commitments[13]);
	copy_pp(commitments[12],commitments[14]);
	// 2QN
	MIPP_gen(1+(int)log2(Q) + (int)log2(N),commitments[15],false,true);
	copy_pp(commitments[15],commitments[16]);
	copy_pp(commitments[15],commitments[17]);
	
	MIPP_gen((int)log2(N*M),commitments[18],true,false);
	
	if(range_proof_method == 2 || range_proof_method == 3){
		MIPP_gen((int)log2(M*N)+(int)log2(Q),commitments[19],false,true);
	}
	else{
		MIPP_gen((int)log2(M*N)+(int)(8),commitments[19],false,true);	
	}

	vector<int> arr(data.G.size()*data.G[0].size());

	MIPP_commit(data.weights,arr,commitments[0]);
	MIPP_commit(data.shifted_max,arr,commitments[1]);
	MIPP_commit(data.max_2,arr,commitments[2]);
	MIPP_commit(data.max_1,arr,commitments[3]);
	MIPP_commit(data.normalized_values,arr,commitments[4]);
	MIPP_commit(data.sqrt,arr,commitments[5]);
	vector<F> poly = convert2vector(data.CS);
	MIPP_commit(poly,arr,commitments[6]);
	MIPP_commit(data.pardon_div,arr,commitments[7]);
	MIPP_commit(data.CS_remainders_bits,arr,commitments[8]);
	MIPP_commit(data.pardon_bits,arr,commitments[9]);
	MIPP_commit(data.inv_relu_bits,arr,commitments[10]);
	MIPP_commit(data.relu_bits,arr,commitments[11]);
	MIPP_commit(data.normalized_bits,arr,commitments[12]);
	MIPP_commit(data.shift_bits,arr,commitments[13]);
	MIPP_commit(data.max_1_bits,arr,commitments[14]);
	MIPP_commit(data.max_2_bits,arr,commitments[15]);
	MIPP_commit(data.sqrt_left_bits,arr,commitments[16]);
	MIPP_commit(data.sqrt_right_bits,arr,commitments[17]);
	
	char buff[256];
	for(int i = 0; i < data.G.size(); i++){
		for(int j = 0; j < data.G[0].size(); j++){
			data.G[i][j].getStr(buff,256,10);
			arr[i*data.G[0].size() + j] = atoi(buff);
		}
	}


	poly = convert2vector(data.G);
	clock_t t1,t2;
	t1 = clock();
	MIPP_commit(poly,arr,commitments[18]);
	t2 = clock();
	printf("Input commit %lf\n",(float)(t2-t1)/(float)CLOCKS_PER_SEC );
	
	vector<F> bits;
	if(range_proof_method == 2 || range_proof_method == 3){
		vector<F> bits = prepare_bit_vector(convert2vector(data.G),Q);
		MIPP_commit(bits,arr,commitments[19]);
		bits.clear();
	}
	else{
		if(Q == 8){
			t1 = clock();
	
			MIPP_predicate_commit(arr,commitments[19]);
			t2 = clock();
			printf("Predicate commit %lf\n",(float)(t2-t1)/(float)CLOCKS_PER_SEC );
	
		}else{
			vector<int> arr2 = arr;
			for(int i = 0; i < arr2.size(); i++){
				arr2[i] = arr[i]%256;
			}
			MIPP_predicate_commit(arr2,commitments[19]);
			MIPP_predicate_commit(arr2,commitments[19]);
		}
	}
}

void FLTrust_Commit(vector<MIPP_Comm> &commitments, FLTrust data,int range_proof_method){
	commitments.resize(5);
	if(range_proof_method == 2 || range_proof_method == 3){
		MIPP_gen((int)log2(convert2vector(data.G).size())+(int)log2(Q),commitments[0],false,true);
	}
	else{
		MIPP_gen((int)log2(convert2vector(data.G).size())+(int)(8),commitments[0],false,true);	
	}
	

	MIPP_gen((int)log2(convert2vector(data.G).size()),commitments[1],true,false);
	
	MIPP_gen((int)log2(data.relu_bits.size()),commitments[2],false,true);
	
	MIPP_gen((int)log2(data.remainder_bits.size()),commitments[3],false,true);
	
	MIPP_gen((int)log2(data.quotients_bits.size()),commitments[4],false,true);
	
	vector<int> arr;
	char buff[256];
	for(int i = 0; i < data.G.size(); i++){
		for(int j = 0; j < data.G[i].size(); j++){
			data.G[i][j].getStr(buff,10,256);
			arr.push_back(atoi(buff));
		}
	}

	vector<F> bits;
	if(range_proof_method == 2 || range_proof_method == 3){
		vector<F> bits = prepare_bit_vector(convert2vector(data.G),Q);
		
		MIPP_commit(bits,arr,commitments[0]);
		bits.clear();
	}
	else{
		if(Q == 8){
			clock_t t1,t2;
			t1 = clock();	
	
			MIPP_predicate_commit(arr,commitments[0]);
			t2 = clock();
			printf("Predicate commit %lf\n",(float)(t2-t1)/(float)CLOCKS_PER_SEC );

		}else{
			vector<int> arr2 = arr;
			for(int i = 0; i < arr2.size(); i++){
				arr2[i] = arr[i]%256;
			}
			MIPP_predicate_commit(arr2,commitments[0]);
			MIPP_predicate_commit(arr2,commitments[0]);
		}
	}
	vector<F> poly = convert2vector(data.G);

	MIPP_commit(data.relu_bits,arr,commitments[2]);
	MIPP_commit(data.remainder_bits,arr,commitments[3]);
	MIPP_commit(data.quotients_bits,arr,commitments[4]);

	clock_t t1,t2;
	t1 = clock();	
	MIPP_commit(poly,arr,commitments[1]);
	t2 = clock();
	printf("Input commit %lf\n",(float)(t2-t1)/(float)CLOCKS_PER_SEC );
	
}


void FoolsGold_Open(vector<MIPP_Comm> &commitments, FoolsGold data, int N, int M,int range_proof_method){
	
	F eval;

	vector<F> x = generate_randomness((int)log2(N),F(0));
	eval = evaluate_vector(data.weights,x);
	MIPP_open(data.weights,x,commitments[0]);
	MIPP_verify(eval,commitments[0]);
	
	eval = evaluate_vector(data.shifted_max,x);
	MIPP_open(data.shifted_max,x,commitments[1]);
	MIPP_verify(eval,commitments[1]);
	
	eval = evaluate_vector(data.max_2,x);
	MIPP_open(data.max_2,x,commitments[2]);
	MIPP_verify(eval,commitments[2]);

	eval = evaluate_vector(data.max_1,x);
	MIPP_open(data.max_1,x,commitments[3]);
	MIPP_verify(eval,commitments[3]);
	
	eval = evaluate_vector(data.normalized_values,x);
	MIPP_open(data.normalized_values,x,commitments[4]);
	MIPP_verify(eval,commitments[4]);
	
	eval = evaluate_vector(data.sqrt,x);
	MIPP_open(data.sqrt,x,commitments[5]);
	MIPP_verify(eval,commitments[5]);

	x = generate_randomness(2*(int)log2(N),F(0));
	eval = evaluate_vector(convert2vector(data.CS),x);
	MIPP_open(convert2vector(data.CS),x,commitments[6]);
	MIPP_verify(eval,commitments[6]);
	
	eval = evaluate_vector(data.pardon_div,x);
	MIPP_open(data.pardon_div,x,commitments[7]);
	MIPP_verify(eval,commitments[7]);

	x = generate_randomness(2+ (int)log2(Q) +2*(int)log2(N),F(0));
	eval = evaluate_vector(data.CS_remainders_bits,x);
	MIPP_open(data.CS_remainders_bits,x,commitments[8]);
	MIPP_verify(eval,commitments[8]);
	
	x = generate_randomness((int)log2(Q) +2*(int)log2(N),F(0));
	eval = evaluate_vector(data.pardon_bits,x);
	MIPP_open(data.pardon_bits,x,commitments[9]);
	MIPP_verify(eval,commitments[9]);
	

	x = generate_randomness((int)(8) +(int)log2(N),F(0));
	
	eval = evaluate_vector(data.inv_relu_bits,x);
	MIPP_open(data.inv_relu_bits,x,commitments[10]);
	MIPP_verify(eval,commitments[10]);
	
	eval = evaluate_vector(data.relu_bits,x);
	MIPP_open(data.relu_bits,x,commitments[11]);
	MIPP_verify(eval,commitments[11]);
	
	x = generate_randomness((int)log2(Q) + (int)log2(N),F(0));
	eval = evaluate_vector(data.normalized_bits,x);
	MIPP_open(data.normalized_bits,x,commitments[12]);
	MIPP_verify(eval,commitments[12]);
	
	eval = evaluate_vector(data.shift_bits,x);
	MIPP_open(data.shift_bits,x,commitments[13]);
	MIPP_verify(eval,commitments[13]);
	
	eval = evaluate_vector(data.max_1_bits,x);
	MIPP_open(data.max_1_bits,x,commitments[14]);
	MIPP_verify(eval,commitments[14]);
	


	x = generate_randomness(1+(int)log2(Q) + (int)log2(N),F(0));
	
	eval = evaluate_vector(data.max_2_bits,x);
	MIPP_open(data.max_2_bits,x,commitments[15]);
	MIPP_verify(eval,commitments[15]);
	
	eval = evaluate_vector(data.sqrt_left_bits,x);
	MIPP_open(data.sqrt_left_bits,x,commitments[16]);
	MIPP_verify(eval,commitments[16]);
	
	eval = evaluate_vector(data.sqrt_right_bits,x);
	MIPP_open(data.sqrt_right_bits,x,commitments[17]);
	MIPP_verify(eval,commitments[17]);
	

	x = generate_randomness((int)log2(M) + (int)log2(N),F(0));
	
	eval = evaluate_vector(convert2vector(data.G),x);
	MIPP_open(convert2vector(data.G),x,commitments[18]);
	MIPP_verify(eval,commitments[18]);

	if(range_proof_method == 2 || range_proof_method == 3){
		x = generate_randomness((int)log2(convert2vector(data.G).size()) + (int)log2(Q),F(0));
		eval = evaluate_vector(prepare_bit_vector(convert2vector(data.G),Q),x);
		MIPP_open(prepare_bit_vector(convert2vector(data.G),Q),x,commitments[19]);
		MIPP_verify(eval,commitments[19]);
	}else{
		x = generate_randomness((int)log2(convert2vector(data.G).size()) + (int)(Q),F(0));
		vector<int> mapping(M*N);
		for(int i = 0; i < M*N; i++){
			mapping[i] = rand()%256;
		}
		//eval = 
		MIPP_predicate_open(mapping,x,commitments[19]);
		if(Q != 8){
			MIPP_predicate_open(mapping,x,commitments[19]);
		}
		//MIPP_verify(eval,commitments[0]);

	}
}

void FLTrust_Open(vector<MIPP_Comm> &commitments,vector<int> &mapping, FLTrust data, int range_proof_method){
	F eval;
	vector<F> x;
	if(range_proof_method == 2 || range_proof_method == 3){
		x = generate_randomness((int)log2(convert2vector(data.G).size()) + (int)log2(Q),F(0));
		eval = evaluate_vector(prepare_bit_vector(convert2vector(data.G),Q),x);
		MIPP_open(prepare_bit_vector(convert2vector(data.G),Q),x,commitments[0]);
		MIPP_verify(eval,commitments[0]);
	}else{
		x = generate_randomness((int)log2(convert2vector(data.G).size()) + (int)(Q),F(0));
		//eval = 
		MIPP_predicate_open(mapping,x,commitments[0]);
		if(Q != 8){
			MIPP_predicate_open(mapping,x,commitments[0]);
		}
		//MIPP_verify(eval,commitments[0]);

	}
	
	x = generate_randomness((int)log2(data.relu_bits.size()),F(0));
	eval = evaluate_vector(data.relu_bits,x);
	MIPP_open(data.relu_bits,x,commitments[2]);
	MIPP_verify(eval,commitments[2]);
	

	x = generate_randomness((int)log2(data.remainder_bits.size()),F(0));
	eval = evaluate_vector(data.remainder_bits,x);
	MIPP_open(data.remainder_bits,x,commitments[3]);
	MIPP_verify(eval,commitments[3]);

	x = generate_randomness((int)log2(data.quotients_bits.size()),F(0));
	eval = evaluate_vector(data.quotients_bits,x);
	MIPP_open(data.quotients_bits,x,commitments[4]);
	MIPP_verify(eval,commitments[4]);


	x = generate_randomness((int)log2(convert2vector(data.G).size()),F(0));
	eval = evaluate_vector(convert2vector(data.G),x);
	MIPP_open(convert2vector(data.G),x,commitments[1]);
	MIPP_verify(eval,commitments[1]);
}
	


void test(vector<F> &arr,int idx){
	int N = 1024*1024*64/threads;
	for(int j = 0; j < 10; j++){
		for(int i = idx*N; i <  idx*N+N; i++){
			arr[i] = arr[i]*arr[i]*arr[i]*arr[i];
		}

	}
}


void compute_powers(F w, vector<F> &powers, int size){
	powers.resize(1<<size);
	powers[0] = w;
	for(int i = 1; i < 1<<size; i++){
		powers[i] = powers[i-1]*w;
	}
}

void compute_products(vector<F> powers, vector<F> &coeff, vector<F> evals){
	coeff.resize(powers.size());
	for(int i = 0; i < coeff.size(); i++){
		coeff[i] = F(0);
	}
	for(int i = 0; i < powers.size(); i++){
		vector<F> temp(powers.size(),F(0));
		F prod = F(1);
		for(int j = 0; j < powers.size(); j++){
			if(j != i){
				prod *= (powers[i] - powers[j]);
			}
		}
		F::inv(prod,prod);
		F c = evals[i]*prod;
		temp[0] = c;
		for(int j = 0; j < powers.size(); j++){
			if(i == j)continue;
			
			for(int k = powers.size()-1; k > 0; k--){
				temp[k] += temp[k-1];
				temp[k-1] = (-temp[k-1]*powers[j]); 
			}
		}
		for(int j = 0; j < powers.size(); j++){
			coeff[j] += temp[j];
		}
	}
}

F univatiate_eval(vector<F> coeff, F x){
	/*F temp = coeff[1] + coeff[0]*x;
	for(int i = 2; i < coeff.size(); i++){
		temp = coeff[i] + temp*x;
	}
	return temp;
	*/
	F temp = coeff[coeff.size()-2] + coeff[coeff.size()-1]*x;
	for(int i = coeff.size()-3; i >= 0; i--){
		temp = coeff[i] + temp*x;
	}
	return temp;
	
}

vector<F> partial_poly(vector<F> coeff, F y){
	int s = (int)sqrt(coeff.size());
	vector<F> poly(s,F(0));
	vector<F> evals(s);
	evals[0] = F(1);
	for(int i = 1; i < s; i++){
		evals[i] = evals[i-1]*y;
	}
	for(int i = 0; i < s; i++){
		for(int j = 0; j < s; j++){
			poly[j] += evals[i] * coeff[i*s + j];
		}
	}
	return poly;

}

vector<F> partial_evals(vector<F> coeff, F rx){
	int s = (int)sqrt(coeff.size());
	vector<F> poly(s,F(0));
	vector<F> evals(s);
	evals[0] = F(1);
	for(int i = 1; i < s; i++){
		evals[i] = evals[i-1]*rx;
	}
	for(int i = 0; i < s; i++){
		for(int j = 0; j < s; j++){
			poly[i] += evals[j] * coeff[i*s + j];
		}
	}
	return poly;	
}

int main(int argc, char *argv[]){
	initPairing(mcl::BN_SNARK1);
	//initPairing(mcl::BLS12_381);
	elliptic_curves_init();
	init_hash();
	

	verification_time = 0.0;
	proving_time = 0.0;
	comm_size = 0;
    range_proof_verification_time = 0.0;
	range_proof_size = 0;

    threads = atoi(argv[4]);
    char buff[257];
    

    /*
	printf("%d\n",threads );
    
    printf("%f\n",proving_time );
	int input_dim;
    
   	int bitsize = atoi(argv[1]) + atoi(argv[2]);
   	MIPP_Comm commitment;
   	printf("%d\n",bitsize );
    vector<int> arr(1<<bitsize);
    for(int i = 0; i < arr.size(); i++){
    	arr[i] = rand()%256;
    }
    MIPP_gen((int)log2(arr.size())+(int)(Q),commitment,false,true);	
	
    MIPP_predicate_commit(arr,commitment);
    printf("Commit = %lf\n",proving_time );
    vector<F> x = generate_randomness(bitsize+Q,F(0));
    proving_time = 0.0;
    MIPP_predicate_open(arr,x,commitment);
    printf("Open = %lf\n",proving_time );
    printf("Proof size : %lf\n", (float)comm_size/1024.0);
   	*/
   	/*

    vector<F> poly = generate_randomness(1<<bitsize,F(0));
    vector<F> x = generate_randomness(bitsize,F(0));
    clock_t cs,ce;
    cs = clock();
    VestaOpenAll(poly);
    ce = clock();
    printf("%lf\n", (float)(ce-cs)/(float)CLOCKS_PER_SEC);
    */
    /*
    Vesta_Comm comm;
    generate_pp_vesta(comm,bitsize);
    clock_t cs,ce;
    cs = clock();
    commit(poly,comm.comm[0]);
    Vesta_Commit(poly,comm,0);
    ce = clock();
    printf("%lf\n",(float)(ce-cs)/(float)CLOCKS_PER_SEC);
    proving_time = 0.0;
    Vesta_OpenAll(poly, comm, 0);
   	printf("%lf\n",proving_time );
   	*/
   	/*
    Comm comm;
    generate_pp(comm,19);
    commit(poly,comm);
    proving_time = 0.0;
    ////hyperproofs_openall(poly,comm);
    Vesta_OpenAll(poly,comm);
    printf("%lf\n",proving_time );
    
    Comm comm2;
    //generate_hyperproofs_pp(comm2,18);
    clock_t cb,ce;
    cb = clock();
    hyperproofs_openall(poly,comm);
    ce = clock();
    printf("Hyperproofs : %lf\n",(float)(ce-cb)/(float)CLOCKS_PER_SEC );
    */

    
   	int N = 1<<atoi(argv[1]);
   	int M = 1<<atoi(argv[2]);
   	// 1 : lookup
   	// 2 : batched range proof
   	// 3 : naive range proof
   	int range_proof_method = atoi(argv[3]);
   	threads = atoi(argv[4]);
   	// 1 : FLTrust
   	// 2 : FoolsGold
   	// 3 : Range Proofs
   	int option = atoi(argv[5]);
   	if(option == 1){	   	
	   	FLTrust data = fltrust(N,M);
	   
	   	vector<F> r = generate_randomness((int)log2(convert2vector(data.G).size()),F(0));
	   	F eval = evaluate_vector(convert2vector(data.G),r);
	   	vector<MIPP_Comm> commitments;
	   	vector<int> input(data.G.size()*data.G[0].size());
	   	
	   	for(int i = 0; i < data.G.size(); i++){
	   		for(int j = 0; j < data.G[0].size(); j++){
	   			data.G[i][j].getStr(buff,256,10);
	   			input[i*data.G[0].size() + j] = atoi(buff);
	   		}
	   	}
	   	
	   	FLTrust_Commit(commitments,data,range_proof_method);
	   	printf("Commit time : %lf\n",proving_time );
	   	float p1 = proving_time;
	   	proving_time = 0;
	   	proof range_proof;
	   	//Range_proof(convert2vector(data.G),r,eval);
	   	if(range_proof_method == 1){
	   		if(Q == 8){
	   			lookup_range_proof(input, 1<<Q);
	   		}else{
	   			for(int i = 0;i < input.size(); i++){
	   				input[i] = input[i]%256;
	   			}
	   			lookup_range_proof(input, 256);
	   			lookup_range_proof(input, 256);
	   		}
	   	}
	   	else if(range_proof_method == 2){
	   		range_proof =_prove_bit_decomposition_folded( prepare_bit_vector(convert2vector(data.G),Q),r,eval,Q);
	   	}else{
	   		range_proof =_prove_bit_decomposition( prepare_bit_vector(convert2vector(data.G),Q),r,eval,Q);   		
	   	}
	   	printf("Range Proof time : %lf\n",proving_time );
		float p2 = proving_time;

	   	proving_time = 0;
	   	vector<proof> proofs = FLTrust_Prove(N,M,data);
	   	float p3 = proving_time;
	   	if(range_proof_method != 1){
	   		proofs.push_back(range_proof);

	   	}
	   	proving_time = 0;
	   	FLTrust_Open(commitments,input,data,range_proof_method);
	   	printf("Open time : %lf\n",proving_time );
	   	printf("Total prove time : %lf\n",proving_time+p1+p2+p3 );
	   	printf("Proof size : %lf\n",(float)comm_size/1024.0 + range_proof_size/1024.0 + get_proof_size(proofs));
	   	printf("Verification time : %lf\n",verify(proofs,M) + range_proof_verification_time + verification_time );
   	}
   	else if(option == 2){
	   	
   		vector<MIPP_Comm> commitments;
   		FoolsGold data = foolsgold(N,M);
   		
   		vector<F> r = generate_randomness((int)log2(convert2vector(data.G).size()),F(0));
	   	F eval = evaluate_vector(convert2vector(data.G),r);
   		vector<int> input(data.G.size()*data.G[0].size());
	   	printf("ok\n");
	   	for(int i = 0; i < data.G.size(); i++){
	   		for(int j = 0; j < data.G[0].size(); j++){
	   			data.G[i][j].getStr(buff,256,10);
	   			input[i*data.G[0].size() + j] = atoi(buff);
	   		}
	   	}

   		FoolsGold_Commit(commitments,data,N,M,range_proof_method);
   		float p1 = proving_time;
   		printf("Commit : %lf\n",proving_time);
   		proving_time = 0.0;
   		proof range_proof;
	   	//Range_proof(convert2vector(data.G),r,eval);
	   	if(range_proof_method == 1){
	   		if(Q == 8){
	   			lookup_range_proof(input, 1<<Q);
	   		}else{
	   			for(int i = 0;i < input.size(); i++){
	   				input[i] = input[i]%256;
	   			}
	   			lookup_range_proof(input, 256);
	   			lookup_range_proof(input, 256);
	   		}
	   	}
	   	else if(range_proof_method == 2){
	   		range_proof =_prove_bit_decomposition_folded( prepare_bit_vector(convert2vector(data.G),Q),r,eval,Q);
	   	}else{
	   		range_proof =_prove_bit_decomposition( prepare_bit_vector(convert2vector(data.G),Q),r,eval,Q);   		
	   	}
	   	printf("Range Proof time : %lf\n",proving_time );
		float p2 = proving_time;
		proving_time = 0.0;

   		vector<proof> proofs = FoolsGold_Prove(N,M,data);
		float p3 = proving_time;
	   	if(range_proof_method != 1){
	   		proofs.push_back(range_proof);
	   	}
	   	printf("FoolsGold : %lf\n",p3 );
	   	proving_time = 0.0;
	   	
		FoolsGold_Open(commitments, data,  N,  M,range_proof_method);
		printf("Open time : %lf\n",proving_time );
	   	printf("Total prove time : %lf\n",proving_time+p1+p2+p3 );
	   	printf("Proof size : %lf\n",(float)comm_size/1024.0 + range_proof_size/1024.0 + get_proof_size(proofs));
	   	printf("Verification time : %lf\n",verify(proofs,M) + range_proof_verification_time + verification_time );
	}
   	else if(option == 3){
   		proof P;
   		vector<proof> proofs;
   		vector<F> arr(N*M);
   		vector<int> arr_int(M*N);
   		for(int i = 0; i < M*N; i++){
   			arr_int[i] = rand()%(1<<Q);
   			arr[i] = F(arr_int[i]);
   		}
   		MIPP_Comm commitment;
   		if(range_proof_method == 2 || range_proof_method == 3 || range_proof_method == 4){
			MIPP_gen((int)log2(M*N)+(int)log2(Q),commitment,false,true);
		}
		else{
			MIPP_gen((int)log2(M*N)+(int)(8),commitment,false,true);	
		}
		

		if(range_proof_method == 2 || range_proof_method == 3 || range_proof_method == 4){
			vector<F> bits = prepare_bit_vector(arr,Q);
			vector<int> temp;
			MIPP_commit(bits,temp,commitment);
			bits.clear();
		}else{
			if(Q == 8){
				MIPP_predicate_commit(arr_int,commitment);
			}else{
				for(int i = 0;i < arr_int.size(); i++){
	   				arr_int[i] = arr_int[i]%256;
	   			}
				MIPP_predicate_commit(arr_int,commitment);
				MIPP_predicate_commit(arr_int,commitment);
			}
		}


		if(range_proof_method == 1){
	   		if(Q == 8){

		   		lookup_range_proof(arr_int, 1<<Q);
	   		}else{
	   			
	   			lookup_range_proof(arr_int, 256);
	   			lookup_range_proof(arr_int, 256);	
	   		}
	   	}
	   	else if(range_proof_method == 2){
	   		vector<F> r = generate_randomness((int)log2(arr.size()),F(0));
	   		P = _prove_bit_decomposition_folded(prepare_bit_vector(arr,Q),r,evaluate_vector(arr,r),Q);
	   		proofs.push_back(P);
	   	}else if(range_proof_method == 4){
			vector<F> bits = prepare_bit_vector(arr,Q);
			vector<F> gkr_input = bits;
			vector<F> powers(8);
			gkr_input.insert(gkr_input.end(),bits.begin(),bits.end());
			gkr_input.insert(gkr_input.end(),arr.begin(),arr.end());
			for(int i = 0; i < 8; i++){
				powers[i].setByCSPRNG();
			}
			gkr_input.insert(gkr_input.end(),powers.begin(),powers.end());
			P = range_proof(gkr_input,powers, arr.size());
			proofs.push_back(P);
		}
	   	else{
	   		vector<F> r = generate_randomness((int)log2(arr.size()),F(0));
	   		P = _prove_bit_decomposition( prepare_bit_vector(arr,Q),r,evaluate_vector(arr,r),Q);   		
			proofs.push_back(P);
	   	}
	   	if(range_proof_method == 2 || range_proof_method == 3 || range_proof_method == 4){
			vector<F> x = generate_randomness((int)log2(M*N) + (int)log2(Q),F(0));
			F eval = evaluate_vector(prepare_bit_vector(arr,Q),x);
			MIPP_open(prepare_bit_vector(arr,Q),x,commitment);
			MIPP_verify(eval,commitment);
		}else{
			vector<F> x = generate_randomness((int)log2(M*N) + (int)(Q),F(0));
			//eval = 
			MIPP_predicate_open(arr_int,x,commitment);
			if(Q != 8){
				MIPP_predicate_open(arr_int,x,commitment);
			}
			//MIPP_verify(eval,commitments[0]);
		}
		printf("Proving time : %lf\n",proving_time);
		printf("Proof size : %lf\n",(float)comm_size/1024.0 + range_proof_size/1024.0 + get_proof_size(proofs));
	   	printf("Verification time : %lf\n",verify(proofs,1) + range_proof_verification_time + verification_time );
   	
   	}
   	else{
   		vector<F> poly(N);
   		for(int i = 0; i < N; i++){
   			poly[i].setByCSPRNG();
   		}
   		if(range_proof_method == 1){
   			printf("Vesta OpenAll\n");
   			VestaOpenAll(poly);
   		}else{
   			printf("Hyperproofs OpenAll\n");
   			Comm pp;
   			generate_pp(pp,(int)log2(N));
   			clock_t s,e;
   			s = clock();
   			commit(poly,pp);
   			hyperproofs_openall(poly,pp);
   			e = clock();
   			printf("OpenAll time : %lf\n",(float)(e-s)/(float)CLOCKS_PER_SEC );
   		}
   	}

   	/* UNIVARIATE CHECK
   	F w = getRootOfUnit(4);
   	F power = w;
   	
   	vector<F> powers;
   	vector<F> coeff;
   	vector<F> evals;
   	for(int i = 0; i < 1<<4; i++){
   		F num;
   		num.setByCSPRNG();
   		evals.push_back(num);
   	}
   	compute_powers(w,powers,4);
   	
   	
   	compute_products(powers,coeff,evals);
   	if(univariate_eval(coeff,w) == evals[0]){
   		printf("ok~\n");
   	}
   	if(univariate_eval(coeff,w*w) == evals[1]){
   		printf("ok~\n");
   	}
   	vector<F> p = partial_poly(coeff,w*w*w*w*w*w*w*w);
   	if(univariate_eval(p,w*w*w*w*w) == evals[4]){
   		printf("ok!\n");
   	}
   	vector<F> px = partial_evals(coeff,F(13));

   	F w2 = getRootOfUnit(2);
   	vector<F> powers2;
   	powers2.push_back(w*w);
   	powers2.push_back(w*w*w*w*w*w);
   	powers2.push_back(w*w*w*w*w*w*w*w*w*w);
   	powers2.push_back(w*w*w*w*w*w*w*w*w*w*w*w*w*w);
   	//compute_powers(w2,powers2,2);
   	vector<F> evals2,coeff2;
   	for(int i = 0; i < 4; i++){
   		evals2.push_back(evals[i*4 + 1]);
   	}
   	compute_products(powers2,coeff2,evals2);
   	F eval1 = univariate_eval(coeff2,F(13));
   	F eval2 = univariate_eval(px,w*w*w*w*w*w*w*w);
   	if(eval1 == eval2){
   		printf("CORRECT\n");
   	}
   	*/
   	
   	/*
   	vector<MIPP_Comm> commitments;
   	FoolsGold data = foolsgold(256,256);
   	FoolsGold_Commit(commitments,data,256,512);
   	printf("Commit : %lf\n",proving_time);
   	proving_time = 0.0;
   	vector<proof> P = FoolsGold_Prove(256,256,data);
	float Vtime  = verify(P);
	printf("Verification time : %lf \n",Vtime );
	printf("%lf kb\n", get_proof_size(P));
	FoolsGold_Open(commitments, data,  256,  512);
	printf("Open : %lf\n",proving_time);
   	*/

   	//lookup_range_proof(num,256);
   	
   	//fold_range_proof(1024*1024*8);

		
   	//verify(r,r[0],commitment);
   	//printf("%d\n",Transcript.size() );
   	/**********************************/
   	// AGGREGATION CIRCUIT

   	/*
   prove_aggr();
	int n = 4*1024*1024;
	vector<F> poly(n);
	for(int i = 0; i < poly.size(); i++){
		poly[i].setByCSPRNG();
	}
	int l = (int)log2(n);
	vector<F> x1(l),x2(l);
	for(int i = 0; i < x1.size(); i++){
		x1[i].setByCSPRNG();
		x2[i].setByCSPRNG();
	}
	F eval1 = evaluate_vector(poly,x1);
	
	F eval2 = evaluate_vector(poly,x2);
   	printf("ok\n");
   	vector<vector<F>> g(x1.size());
   	for(int i = 0; i < x1.size(); i++){
   		g[i].push_back(x1[i]);
   		g[i].push_back(x2[i] - x1[i]);
   	}
   	clock_t start,end;
   	start = clock();
   	vector<F> p = reduce_poly(g, poly);
   	end = clock();
   	printf("%f\n",  (float)(end-start)/(float)CLOCKS_PER_SEC);
   	if(univariate_eval(p,0) == eval1){
   		printf("OK\n");
   	}
   	if(univariate_eval(p,1) == eval2){
   		printf("OK\n");
   	}
	*/
   	/**********************************/
    
   	/*
   	vector<vector<F>> num(2);
   	for(int i = 0; i <2 ; i++){
   		for(int j = 0; j < 16; j++){
   			//num[i].push_back(quantize(-0.1));
   			num[i].push_back(quantize(-(float)rand() / (float)RAND_MAX));
   		}
   	}

   	prove_lookup(num);
	*/
   	
   	/*
   	vector<struct proof> Pr;
   	vector<F> x(1);
   	x[0].setByCSPRNG();
   	if(mimc_multihash2(x)[1] == mimc_multihash3(x)[0][8]){
   		printf("OK\n");
   	}

   	vector<vector<F>> M1(16),M2(16);
   	for(int i = 0; i < M1.size(); i++){
   		M1[i].resize(16);
   		M2[i].resize(16);	
   	}
   	for(int i = 0; i < 16; i++){
   		for(int j = 0; j < 16; j++){
   			M1[i][j].setByCSPRNG();
   			M2[i][j].setByCSPRNG();	
   		}
   	}
   	r.resize(8);
   	for(int i = 0; i < 8; i++){
   		r[i].setByCSPRNG();
   	}
   	vector<vector<F>> M3 = matrix2matrix(M1,M2);
   	struct proof P = _prove_matrix2matrix(M1, M2, r, evaluate_vector(convert2vector(M3),r));
   	

   	Pr.push_back(P);
   	
   	vector<F> arr(1024);
   	for(int i = 0; i < arr.size(); i++){
   		arr[i] = quantize((float)rand() / (float)RAND_MAX);
   	}
   	r.clear();
   	
   	r.resize(10);
   	for(int i = 0; i < 10; i++){
   		r[i].setByCSPRNG();
   	}
   	Pr.push_back(_prove_bit_decomposition( prepare_bit_vector(arr,32),r,  evaluate_vector(arr,r),32));
   	r.push_back(r[0]);
   	r.resize(11);
   	for(int i = 0; i < 11; i++){
   		r[i].setByCSPRNG();
   	}
   	vector<F> arr(1024);
   	for(int i = 0; i < arr.size(); i++){
   		arr[i] = quantize((float)rand() / (float)RAND_MAX);
   	}
   	vector<F> gkr_input;
   	gkr_input.insert(gkr_input.begin(),arr.begin(),arr.end());
   	gkr_input.insert(gkr_input.begin(),arr.begin(),arr.end());
   	gkr_input.insert(gkr_input.begin(),arr.begin(),arr.end());
   	gkr_input.insert(gkr_input.begin(),arr.begin(),arr.end());
   	Pr.push_back(gkr_proof("relu_circuit_input_2048.pws","data",gkr_input,r,false));
	verify_hashes(Pr);
   	*/
   	
   	/*
   	vector<F> arr(4);
   	for(int i = 0; i < 4; i++){
   		arr[i].setByCSPRNG();
   	}
   	vector<vector<F>> hashes = mimc_multihash3(arr);
   	vector<F> test = mimc_multihash2(arr);
   	for(int i = 0; i < arr.size(); i++){
   		if(hashes[i][8] == test[i+1]){
   			printf("ok\n");
   		}
   	}

   	vector<F> gkr_data;
   	gkr_data.insert(gkr_data.end(),arr.begin(),arr.end());
   	for(int i = 0; i < hashes.size(); i++){
   		gkr_data.insert(gkr_data.end(),hashes[i].begin(),hashes[i].end());
   	}
   	
   	vector<F> params = get_parameters();
   	gkr_data.insert(gkr_data.end(),params.begin(),params.end());
   	gkr_data.push_back(F(0));
   	printf("%d\n",gkr_data.size() );

   	
   	gkr_proof("hash_function_eval.pws","file",gkr_data,r,true);
	*/

    /*
	initialize_model();
	struct feedforward_proof P = prove_forward_propagation();
	//P = prove_back_propagation(P);
	int hashes = 0;
	int polynomials = 0;
	for(int i = 0; i < P.proofs.size(); i++){
		for(int j = 0; j < P.proofs[i].randomness.size(); j++){
			hashes += P.proofs[i].randomness[j].size();
		}
		polynomials += P.proofs[i].q_poly.size();
		polynomials += P.proofs[i].c_poly.size();
	
	}
	printf("Hashes : %d, %d\n",hashes, polynomials );
	verify_MLP(P);

	*/
    
 
	
	
	/*
	printf("=======\n");
	for(int i = 0; i < data[4].size(); i++){
		char buff[256];
		data[4][i].getStr(buff,256,10);
		printf("%s\n",buff );
	}
	*/
	//prove_convolution(data[1],data[0],x,w,prod,data[3],P);
	
	/*
	vector<F> data;
	for(int i = 0; i < 4*1024*256; i++){
		F num;
		num.setByCSPRNG();
		data.push_back(num);
	}

	string filename = "input_" + to_string(data.size()/4);
	char name[filename.length()+1];
	strcpy(name, filename.c_str());
	
	string circuit_filename = "range_" + to_string(data.size()/4) + ".pws";
	char circuit_name[circuit_filename.length()+1];
	strcpy(circuit_name, circuit_filename.c_str());
	

	write_data(data,name);
	generate_GKR_proof(circuit_name,name);
	clock_t start,end;
	start = clock();
	generate_2product_sumcheck_proof(data,data);
	end = clock();
	printf("%f\n",(float)(end-start)/(float)CLOCKS_PER_SEC );
	*/
	/*
	string filename = "input";
	char name[filename.length()+1];
	strcpy(name, filename.c_str());
	write_data(nums,name);

	filename = "test.pws";
	char cir[filename.length()+1];
	strcpy(cir, filename.c_str());
	
	generate_proof(cir,name);
	*/
	/*
	printf("Test1\n");
	//auto total_time = std::chrono::high_resolution_clock::now();
	//auto total_end = std::chrono::high_resolution_clock::now();
	//total_time = total_time - total_end;
	
	
	printf("%lf\n",total_time );
	*/

	
	/*
	printf("Test2\n");
	vector<F> nums;
	for(int i = 0; i < 16*1024; i++){
		F num;
		num = F(i);
		nums.push_back(num);
	}
	vector<F> bits = prepare_bit_vector(nums);
	prove_relu(nums,bits);
	*/

	//Pr = prove_bit_decomposition(bits,nums);
	//verify_bit_decomposition(Pr,nums);
	
	//test();
	//Pr = prove_matrix2matrix(M[0],M[1]);
	//verify_matrix2matrix(Pr,M[0],M[1]);

	return 0;
}