#include <stdio.h>
//#include <mcl/bn256.hpp>
#include <mcl/bls12_381.hpp>
//#include <mcl/bn.h>
#include <vector>
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include <time.h>
#include <time.h>
#include <chrono>
#include "utils.hpp"
#include "Poly_Commit.h"
#include <thread>
#include "OpenAll.h"
#include <chrono>
#include "sumcheck.h"
#include "GKR.h"
#include "mimc.h"

using namespace std::chrono;

using namespace mcl::bn;

#define F Fr


#define F_ONE (Fr::one())
#define F_ZERO (Fr(0))
extern int partitions;
using namespace std;
double proving_time = 0.0;
double verification_time;
int comm_size = 0;

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
int ps = 0;
double vt = 0.0;
vector<int> predicates_size;
int application;
int offset = 3;

void batch_VSS(int log_clients, int batch_size){
	int N = 1ULL<<(--log_clients);
	VC_pp pp;
	MIPP_Comm pp_pc,pp_input;
	generate_pp_VC((int)log2(2*N),pp);
	pp_pc.pp1 = pp.pp1;
	pp_pc.pp2 = pp.pp2;
	pp_pc.precompute = false;
	pp_pc.bits = false;
	pp_pc.base = pp.base;
	pp_pc.G = pp.G;
	pp_pc.H = pp.H;
	pp_pc.u = pp.u;
	pp_pc.w = pp.w;
	
	pp_pc.bit_size = pp.bit_size;
	pp_pc.commit_bit_size = pp.commit_bit_size;
	MIPP_gen((int)log2(N*batch_size),pp_input,false,false);
	vector<G1> partial_commitments;
	GT C;
	vector<int> v_int;
	auto start = std::chrono::high_resolution_clock::now();

	vector<vector<F>> v(batch_size),poly(batch_size),shares(batch_size); //v(N),poly(N),shares(2*N,F(0));
	for(int i = 0; i < v.size(); i++){
		v[i].resize(N);
		poly[i].resize(N);
		shares[i].resize(2*N,F(0));
		for(int j = 0; j < N; j++){
			v[i][j] = F(rand());
			poly[i][j] = v[i][j];
		}
	}
	for(int i = 0; i < v.size(); i++){
		fft(poly[i],log_clients,true);
		for(int j = 0; j < N; j++){
			shares[i][j] = poly[i][j];
		}
	}
	for(int i = 0; i < v.size(); i++){
		fft(shares[i],log_clients+1,false);	
	}
	
	auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
    
    std::cout << "Evaluation time: " << duration.count() << " seconds" << std::endl;
	vector<F> v_poly = convert2vector(v);
	start = std::chrono::high_resolution_clock::now();
	vector<F> reduced_v(2*N);
	vector<F> buff(batch_size);
	vector<F> r2((int)log2(batch_size));
	for(int i = 0; i  < r2.size(); i++){
		r2[i].setByCSPRNG();
	}
	for(int i = 0; i < 2*N; i++){
		for(int j = 0; j < batch_size; j++){
			buff[j] = shares[j][i];
		}
		reduced_v[i] = evaluate_vector(buff,r2);
	}
	
	MIPP_commit(v_poly,v_int,pp_input);
	VC_Commit(reduced_v,partial_commitments,C,pp);

	vector<F> r1 = OpenAll(reduced_v, partial_commitments, pp, pp_pc);
	
	vector<F> r;
	for(int i = 0; i < r1.size(); i++)r.push_back(r1[i]);
	for(int i = 0; i < r2.size(); i++)r.push_back(r2[i]);
	printf("%d,%d,%d\n",r1.size(),r2.size(),(int)log2(shares.size()*shares[0].size()));
	proof P1 = prove_fft_matrix(poly,r,evaluate_matrix(shares,r2,r1));
	printf("OK\n");
	proof P2 = prove_ifft_matrix(v,P1.randomness[0],P1.vr[1]);
	
	MIPP_open(v_poly,P2.randomness[0],pp_input);
	stop = std::chrono::high_resolution_clock::now();
    duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
    
    std::cout << "Prove time: " << duration.count() << " seconds" << std::endl;
	std::cout << "Proof size: " << (ps+comm_size)/1024.0 << " KB" << std::endl;
	std::cout << "Verification time: " << vt << " seconds" << std::endl;


}


void VSS(int log_clients){
	int N = 1ULL<<(--log_clients);
	VC_pp pp;
	MIPP_Comm pp_pc,pp_input;
	generate_pp_VC((int)log2(2*N),pp);
	pp_pc.pp1 = pp.pp1;
	pp_pc.pp2 = pp.pp2;
	pp_pc.precompute = false;
	pp_pc.bits = false;
	pp_pc.base = pp.base;
	pp_pc.G = pp.G;
	pp_pc.H = pp.H;
	pp_pc.u = pp.u;
	pp_pc.w = pp.w;
	
	pp_pc.bit_size = pp.bit_size;
	pp_pc.commit_bit_size = pp.commit_bit_size;
	MIPP_gen((int)log2(N),pp_input,false,false);
	vector<G1> partial_commitments;
	GT C;
	vector<int>v_int;
	auto start = std::chrono::high_resolution_clock::now();

	vector<F> v(N),poly(N),shares(2*N,F(0));
	F r;r.setByCSPRNG();
	v[0] = rand();
	for(int i = 1; i < N; i++){
		v[i] = F(rand());
	}
	for(int i = 0; i < poly.size(); i++){
		poly[i] = v[i];
	}
	fft(poly,log_clients,true);
	for(int i = 0; i < N; i++){
		shares[i] = poly[i];
	}
	fft(shares,log_clients+1,false);
	auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
    
    std::cout << "Evaluation time: " << duration.count() << " seconds" << std::endl;



	start = std::chrono::high_resolution_clock::now();
	MIPP_commit(v,v_int,pp_input);
	VC_Commit(shares,partial_commitments,C,pp);
	vector<F> r1 = OpenAll(shares, partial_commitments, pp, pp_pc);
	proof P1 = prove_fft(poly,r1,evaluate_vector(shares,r1));
	proof P2 = prove_ifft(shares,P1.randomness[0],P1.vr[1]);
	MIPP_open(v,P2.randomness[0],pp_input);
	stop = std::chrono::high_resolution_clock::now();
    duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
    
    std::cout << "Prove time: " << duration.count() << " seconds" << std::endl;
	std::cout << "Proof size: " << (ps+comm_size)/1024.0 << " KB" << std::endl;
	std::cout << "Verification time: " << vt << " seconds" << std::endl;
	
}


void our_many_to_one_prove(int size, int seg_size){
	int N = size;
	vector<F> r(10);
	for(int i = 0; i < 10; i++){
		r[i].setByCSPRNG();
	}
	vector<F> data(N);
	data[0] = r[9];
	for(int i = 1; i < N; i++){
		data[i] = data[i-1]*r[0];
	}
	if(seg_size == 1){
		VC_pp pp;
		MIPP_Comm pp_pc,pp_input;
		
		generate_pp_VC((int)log2(N),pp);
		pp_pc.pp1 = pp.pp1;
		pp_pc.pp2 = pp.pp2;
		pp_pc.precompute = false;
		pp_pc.bits = false;
		pp_pc.base = pp.base;
		pp_pc.G = pp.G;
		pp_pc.H = pp.H;
		pp_pc.u = pp.u;
		pp_pc.w = pp.w;
		
		pp_pc.bit_size = pp.bit_size;
		pp_pc.commit_bit_size = pp.commit_bit_size;
		vector<G1> partial_commitments;
		GT C;
		vector<int>v_int;
		
		auto start = std::chrono::high_resolution_clock::now();
		
		VC_Commit(data,partial_commitments,C,pp);
		auto stop = std::chrono::high_resolution_clock::now();
		auto duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
		double pt = duration.count();
		
		prove_multree(data,r,N);
		
		start = std::chrono::high_resolution_clock::now();
		OpenAll(data, partial_commitments, pp, pp_pc);
		stop = std::chrono::high_resolution_clock::now();
		duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
		pt += duration.count();
		pt += proving_time;
		std::cout << "Prove time: " << pt << " seconds" << std::endl;
		std::cout << "Proof size: " << (ps+comm_size)/1024.0 << " KB" << std::endl;
		std::cout << "Verification time: " << vt << " seconds" << std::endl;
	}else{
		VC_pp pp;
		MIPP_Comm pp_pc,pp_input;
		MIPP_gen((int)log2(N),pp_input,false,false);
		generate_pp_VC((int)log2(N/seg_size),pp);
		pp_pc.pp1 = pp.pp1;
		pp_pc.pp2 = pp.pp2;
		pp_pc.precompute = false;
		pp_pc.bits = false;
		pp_pc.base = pp.base;
		pp_pc.G = pp.G;
		pp_pc.H = pp.H;
		pp_pc.u = pp.u;
		pp_pc.w = pp.w;
		
		pp_pc.bit_size = pp.bit_size;
		pp_pc.commit_bit_size = pp.commit_bit_size;
		vector<G1> partial_commitments;
		GT C;
		vector<int>v_int;
		
		auto start = std::chrono::high_resolution_clock::now();
		
		MIPP_commit(data,v_int,pp_input);
		vector<F> r_p((int)log2(seg_size));
		vector<F> beta_p;precompute_beta(r_p,beta_p);
		vector<F> partitions(N/seg_size,F(0));
		
		for(int i = 0; i < N/seg_size; i++){
			for(int j = 0; j < seg_size; j++){
				partitions[i] += beta_p[j]*data[i*seg_size + j];
			}
		}
		
		VC_Commit(partitions,partial_commitments,C,pp);
		auto stop = std::chrono::high_resolution_clock::now();
		auto duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
		double pt = duration.count();
		
		prove_multree(data,r,N);
		
		start = std::chrono::high_resolution_clock::now();
		MIPP_open(data,r,pp_input);
		OpenAll(partitions, partial_commitments, pp, pp_pc);
		stop = std::chrono::high_resolution_clock::now();
		duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
		pt += duration.count();
		pt += proving_time;
		std::cout << "Prove time: " << pt << " seconds" << std::endl;
		std::cout << "Proof size: " << (ps+comm_size)/1024.0 << " KB" << std::endl;
		std::cout << "Verification time: " << vt << " seconds" << std::endl;
	}
	
}


void hyperproofs_prove(int size, int seg_size){
	Comm pp_pc;
	int N = size;
	generate_pp_hyperproofs(pp_pc,(int)log2(size));
	vector<F> r((int)log2(size));
	for(int i = 0; i <(int)log2(size); i++){
		r[i].setByCSPRNG();
	}
	vector<F> data(N);
	vector<int> data_int;
	data[0] = r[0];
	for(int i = 1; i < N; i++){
		data[i] = data[i-1]*r[0];
	}
		auto start = std::chrono::high_resolution_clock::now();
	
	printf("%d\n",data.size());
	commit(data,pp_pc);
	//MIPP_commit(data,data_int,pp_pc);
	auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
    double pt = duration.count();
	std::cout << "Commit time: " << pt << " seconds" << std::endl;
	prove_multree(data,r,N);
	
	start = std::chrono::high_resolution_clock::now();
	vector<G1> P;
	open(data,r,pp_pc.base,P);
	hyperproofs_openall(data,pp_pc.base);

	stop = std::chrono::high_resolution_clock::now();
    duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
    pt += duration.count();
	pt += proving_time;
    verify_proof(r,pp_pc.pp2,pp_pc.H,P);
	for(int i = 0; i < seg_size/2; i++){
		verify_proof(r,pp_pc.pp2,pp_pc.H,P);
	}
	ps += (2)*(P.size()+1)*48;
    ps += 2*(seg_size-1)*48;
	std::cout << "Prove time: " << pt << " seconds" << std::endl;
	std::cout << "Proof size: " << (ps+comm_size)/1024.0 << " KB" << std::endl;
	std::cout << "Verification time: " << vt << " seconds" << std::endl;
}

void MT_prove(int size){

	MIPP_Comm pp_pc;
	int N = size;
	MIPP_gen((int)log2(2*partitions*N),pp_pc,false,false);
	vector<F> r((int)log2(size));
	for(int i = 0; i < 10; i++){
		r[i].setByCSPRNG();
	}
	vector<F> data(2*partitions*N);
	vector<int> data_int;
	data[0] = r[9];
	for(int i = 1; i < 2*partitions*N; i++){
		data[i] = data[i-1]*r[0];
	}
		auto start = std::chrono::high_resolution_clock::now();
	
	MIPP_commit(data,data_int,pp_pc);
	auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
    double pt = duration.count();
    
	prove_multree(data,r,N);
	
	start = std::chrono::high_resolution_clock::now();
	mimc_sumcheck(data);
	MIPP_open(data,r,pp_pc);
	stop = std::chrono::high_resolution_clock::now();
    duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
    pt += duration.count();
	pt += proving_time;
    std::cout << "Prove time: " << pt << " seconds" << std::endl;
	std::cout << "Proof size: " << (ps+comm_size)/1024.0 << " KB" << std::endl;
	std::cout << "Verification time: " << vt << " seconds" << std::endl;

}


void standard_prove(int size){
	MIPP_Comm pp_pc;
	int N = size;
	MIPP_gen((int)log2(size),pp_pc,false,false);
	vector<F> r((int)log2(size));
	for(int i = 0; i < 10; i++){
		r[i].setByCSPRNG();
	}
	vector<F> data(N);
	vector<int> data_int;
	data[0] = r[9];
	for(int i = 1; i < N; i++){
		data[i] = data[i-1]*r[0];
	}
		auto start = std::chrono::high_resolution_clock::now();
	
	MIPP_commit(data,data_int,pp_pc);
	auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
    double pt = duration.count();
    
	prove_multree(data,r,N);
	
	start = std::chrono::high_resolution_clock::now();
	MIPP_open(data,r,pp_pc);
	stop = std::chrono::high_resolution_clock::now();
    duration = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
    pt += duration.count();
	pt += proving_time;
    std::cout << "Prove time: " << pt << " seconds" << std::endl;
	std::cout << "Proof size: " << (ps+comm_size)/1024.0 << " KB" << std::endl;
	std::cout << "Verification time: " << vt << " seconds" << std::endl;
}

int main(int argc, char *argv[]){
	initPairing(mcl::BN_SNARK1);
	init_hash();
	//initPairing(mcl::BLS12_381);
	
	vector<G1> A(1ULL<<atoi(argv[1])),w(1ULL<<atoi(argv[1]));
	vector<G2> u(1ULL<<atoi(argv[1]));
	vector<F> b(1ULL<<atoi(argv[1]));
	G1 G;
	G2 H;
	for(int i = 0; i < b.size(); i++){
		b[i].setByCSPRNG();
	}
	char rand[256];
	for(int i = 0; i < 256; i++){
		rand[i] = i+'4';
	}
	
	//commitment.G = mcl::bn::getG1basePoint();
	mcl::bn::hashAndMapToG1(G,rand,256);

	mcl::bn::hashAndMapToG2(H,rand,256);
	for(int i = 0; i < A.size(); i++){
		A[i] = G*b[i];
		w[i] = G*b[i];
		u[i] = H*b[i];
	}
	GT T;
	mcl::bn::pairing(T,G,H);
	
	clock_t t1,t2;
	t1 = clock();
	MIPP(A, u, b, w, T, G, G, H,H);
	t2 = clock();
	printf("%lf\n",(atoi(argv[1]))*(double)(t2-t1)/(double)CLOCKS_PER_SEC);
	exit(-1);

	verification_time = 0.0;
	proving_time = 0.0;
	comm_size = 0;
    range_proof_verification_time = 0.0;
	range_proof_size = 0;

	application = atoi(argv[1]);

	if(application == 1){
		VSS(atoi(argv[2]));
	}else if(application == 2){
		batch_VSS(atoi(argv[2]),1ULL<<atoi(argv[3]));
	}
	else{
		if(atoi(argv[2]) == 1){
			our_many_to_one_prove(1ULL<<atoi(argv[3]),1ULL<<atoi(argv[4]));
		}else if(atoi(argv[2]) == 2){
			standard_prove(1ULL<<atoi(argv[3]));
		}else if(atoi(argv[2]) == 3){
			hyperproofs_prove(1ULL<<atoi(argv[3]),1ULL<<atoi(argv[4]));
		}else{
			partitions = atoi(argv[4]);
			MT_prove(1ULL<<atoi(argv[3]));
		}
	}



	return 0;
}