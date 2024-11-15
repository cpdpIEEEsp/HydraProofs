#include "config_pc.hpp"
#include <math.h>
#include "utils.hpp"
#include "mimc.h"
#include "sumcheck.h"
extern double vt;
extern int ps;
F current_randomness;
extern int partitions;

struct proof generate_4product_sumcheck_proof(vector<F> &v1, vector<F> &v2,F previous_r){
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(v1.size()));
	vector<quadruple_poly> p;
	F rand = previous_r;
	current_randomness = previous_r;
	vector<F> r;
	for(int i = 0; i < rounds; i++){
		quadruple_poly poly = quadruple_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		
		linear_poly l1,l4;
		
		int L = 1 << (rounds -1- i);
		for(int j = 0; j < L; j++){
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			//q1 = quadratic_poly()
			l4 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
			//l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
			temp_poly = l1*l1*l1;
			poly = poly + temp_poly*l4;

			v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
			v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
		}
		r.push_back(rand);
		vector<F> input;
		clock_t t1,t2;
		t1 = clock();
		mimc_hash(poly.a,current_randomness);
		mimc_hash(poly.b,current_randomness);
		mimc_hash(poly.c,current_randomness);
		mimc_hash(poly.d,current_randomness);
		mimc_hash(poly.e,current_randomness);
		t2 = clock();
		vt += (double)(t2-t1)/CLOCKS_PER_SEC;
		ps += 5*sizeof(F);
		//mimc_hash(poly.a,rand);
		
		//input.push_back(rand);
		//input.push_back(poly.a);
		//input.push_back(poly.b);
		//input.push_back(poly.c);
		//input.push_back(poly.d);
		//vector<vector<F>> temp = mimc_multihash3(input);
		//Pr.w_hashes.push_back(temp);
		//rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		rand = current_randomness;
		p.push_back(poly);
	}
	Pr.quad_poly = p;
	Pr.randomness.push_back(r);
	mimc_hash(v1[0],current_randomness);
	mimc_hash(v2[0],current_randomness);
	
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v2[0]);
	
	return Pr;
}


void extend_input(vector<F> input, vector<F> extended_input, int partitions){
	vector<F> buff;
	for(int i = 0; i < input.size()/2; i++){
		buff = mimc_hash_segments(input[2*i],input[2*i+1]);
		for(int j = 0; j < partitions; j++){
			extended_input[j*input.size()/2 + i] = buff[j];
		}
	}
}


vector<proof> mimc_sumcheck(vector<F> input){
	proof P;
	int rounds = 80/partitions;
	pad_vector(input);
	vector<F> extended_input(input.size()*partitions/2);
	extend_input(input,extended_input,partitions);
	vector<vector<F>> data(rounds);
	vector<vector<F>> C_M(partitions);
	vector<F> C = get_parameters();
	
	clock_t start,end;
	start = clock();
	
	int counter = 0;
	for(int i = 0; i < partitions; i++){
		C_M[i].resize(rounds);
		for(int j = 0; j < rounds; j++){
			C_M[i][j] = C[counter];
			counter++;
		}
	}
	
	data[0] = extended_input;
	for(int i = 1; i < rounds; i++){
		data[i].resize(extended_input.size());
		for(int j = 0; j < input.size()/2; j++){
			for(int k = 0; k < partitions; k++){
				data[i][ k*input.size()/2 + j] = (data[i-1][k*input.size()/2 + j] + C_M[k][i])*(data[i-1][k*input.size()/2 + j] + C_M[k][i])*(data[i-1][k*input.size()/2 + j] + C_M[k][i]);  
			}
		}
	}
	
	
	vector<F> x = generate_randomness((int)log2(extended_input.size()),current_randomness);
	F sum = evaluate_vector(data[rounds-1],x);
	
	vector<F> beta;
	vector<F> v(data[0].size());
	vector<proof> proofs;

	for(int i = rounds-2; i >= 0; i--){
		
		precompute_beta(x,beta);

		vector<F> temp_c;
		for(int j = 0; j < partitions; j++){
			temp_c.push_back(C_M[j][i+1]);
		}
		for(int j = 0; j < input.size()/2; j++){
			for( int k = 0; k < partitions; k++){
				v[k*input.size()/2 + j] = data[i][k*input.size()/2 + j] + C_M[k][i+1];
			}
		}
		P = generate_4product_sumcheck_proof(v, beta,current_randomness);
		proofs.push_back(P);
		if(P.quad_poly[0].eval(F(0))  +P.quad_poly[0].eval(F(1)) != sum){
			printf("Error %d\n",i);
		}
		// check correctness
		x = P.randomness[0];
		
		vector<F> x_c;
		for(int j = x.size()-(int)log2(partitions); j < x.size(); j++ ){
			x_c.push_back(x[j]);
		}
		sum = P.vr[0] - evaluate_vector(temp_c,x_c);
		// compute new sum
	}
	end = clock();
	//printf("Hash prove time : %lf \n",(float)(end-start)/(float)CLOCKS_PER_SEC);
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
	return proofs;

}


struct proof generate_2product_sumcheck_proof(vector<F> &_v1, vector<F> &_v2, F previous_r){
	struct proof Pr;
	vector<F> r;// = generate_randomness(int(log2(v1.size())));
	F rand = previous_r;
	vector<quadratic_poly> p;
	int rounds = int(log2(_v1.size()));
	
	F *v1 = (F *)malloc(_v1.size()*sizeof(F)/2);
	F *v2 = (F *)malloc(_v2.size()*sizeof(F)/2);
	clock_t t1,t2;
	for(int i = 0; i < rounds; i++){
		quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		
        quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		linear_poly l1,l2;
		int L = 1 << (rounds - 1-i);
		for(int j = 0; j < L; j++){
			if(i== 0){
				l1 = linear_poly(_v1[2*j+1] - _v1[2*j],_v1[2*j]);
				l2 = linear_poly(_v2[2*j+1] - _v2[2*j],_v2[2*j]);
				temp_poly = l1*l2;
				poly = poly + temp_poly;
			}else{
				l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
				l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
				temp_poly = l1*l2;
				poly = poly + temp_poly;
			}
		}
		clock_t t1,t2;
		t1 = clock();
		rand = mimc_hash(rand,poly.a);
		rand = mimc_hash(rand,poly.b);
		rand = mimc_hash(rand,poly.c);
		ps += 3*sizeof(F);
        r.push_back(rand);	
		p.push_back(poly);
		poly.eval(rand);
		poly.eval(F(1)) + poly.eval(F(0));
		t2 = clock();
		vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
		for(int j = 0; j < L; j++){
			if(i == 0){
				v1[j] = _v1[2*j] + rand*(_v1[2*j+1]-_v1[2*j]);
				v2[j] = _v2[2*j] + rand*(_v2[2*j+1]-_v2[2*j]);					
			
			}else{
				v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
				v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);					
			}
		}
	}
        
	rand = mimc_hash(rand,v1[0]);
	rand = mimc_hash(rand,v2[0]);
	
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v2[0]);
	Pr.q_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = rand;
	free(v1);
	free(v2);
	
	return Pr;
 }



struct proof prove_fft(vector<F> M, vector<F> r, F previous_sum){
	M.resize(2*M.size());
	

	vector<F> Fg1(M.size()); 
	phiGInit(Fg1,r.begin(),F(1),r.size(),false);
	struct proof Pr = generate_2product_sumcheck_proof(Fg1,M,r[r.size()-1]);
	
	
	
	if(previous_sum != (Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1))){
		printf("Error in fft\n");
		exit(-1);
	}
	
	//Pr.randomness.push_back(r1); 
	//Pr.randomness.push_back(r2);
	return Pr;
}



struct proof prove_ifft(vector<F> M, vector<F> r, F previous_sum){
	F scale = F(M.size());
    F::inv(scale, scale);
	
	
	vector<F> Fg(M.size());
	clock_t start,end;
	start = clock();
	phiGInit(Fg,r.begin(),scale,r.size(),true);
	struct proof Pr = generate_2product_sumcheck_proof(Fg,M,r[r.size()-1]);
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;

	if(previous_sum != (F(1)-r[int(log2(M.size()))])*(Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1))){
		printf("Error in ifft\n");
		//exit(-1);
	}
	
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
	

	vector<F> arr(M[0].size(),F(0));
    vector<F> B;precompute_beta(r1,B);
    for(int i = 0; i < M.size(); i++){
        for(int j = 0; j < M[0].size(); j++){
            arr[j] += B[i]*M[i][j];
        }
    }
    
	
	vector<F> Fg1(M[0].size()); 
	phiGInit(Fg1,r2.begin(),F(1),r2.size(),false);
	struct proof Pr = generate_2product_sumcheck_proof(Fg1,arr,r[r.size()-1]);
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;

	
	
	if(previous_sum != (Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1))){
		printf("Error in fft\n");
		//exit(-1);
	}
	for(int i = 0; i < r1.size(); i++){
		Pr.randomness[0].push_back(r1[i]);
	}
	//Pr.randomness.push_back(r1); 
	//Pr.randomness.push_back(r2);
	return Pr;
}

struct proof prove_ifft_matrix(vector<vector<F>> M, vector<F> r, F previous_sum){
	F scale = F(M[0].size());
	F::inv(scale,scale);
    
	//F::inv(scale,M[0].size());
	vector<F> r1,r2;
	
	for(int i = 0; i < int(log2(M[0].size())); i++){
		r2.push_back(r[i]);
	}
	for(int i = 0; i < int(log2(M.size())); i++){
		r1.push_back(r[i+1+int(log2(M[0].size()))]);
	}
	
	vector<F> Fg(M[0].size());
	clock_t start,end;
	start = clock();
	vector<F> arr(M[0].size(),F(0));
    vector<F> B;precompute_beta(r1,B);
    for(int i = 0; i < M.size(); i++){
        for(int j = 0; j < M[0].size(); j++){
            arr[j] += B[i]*M[i][j];
        }
    }
    phiGInit(Fg,r2.begin(),scale,r2.size(),true);
	struct proof Pr = generate_2product_sumcheck_proof(Fg,arr,r[r.size()-1]);
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;

	if(previous_sum != (F(1)-r[int(log2(M[0].size()))])*(Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1))){
		printf("Error in ifft\n");
		//exit(-1);
	}
	
	for(int i = 0; i < r1.size(); i++){
		Pr.randomness[0].push_back(r1[i]);
	}
	return Pr;
}
