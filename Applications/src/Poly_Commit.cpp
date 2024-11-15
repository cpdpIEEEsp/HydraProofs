#include "Poly_Commit.h"
#include "utils.hpp"
#include <math.h>
#include <map>
#include <unordered_map>
#include <thread>
#include <chrono>

using namespace std::chrono;

extern double proving_time;
extern double verification_time;
extern int comm_size;
extern int threads;
extern double vt;
extern int ps;
int Q = 16;
extern int offset;

vector<F> arr_difference(F x1, F x2, vector<F> &arr){
	vector<F> diff(arr.size()/2);
	if(x1 == F(1) && x2 == F(1)){
		for(int i = 0; i < arr.size()/2; i++){
			diff[i] = arr[2*i + 1] - arr[2*i];
		}
	}else{
		for(int i = 0; i < arr.size()/2; i++){
			diff[i] = x1*(arr[2*i + 1] - arr[2*i]) + arr[2*i];
		}
	}

	//for(int i = 0; i < arr.size()/2; i++){
	//	diff[i] = x1*arr[2*i + 1] - x2*arr[2*i];
	//}
	return diff;
}

vector<F> compute_coefficients(vector<F> &arr){
	
	if(arr.size() == 1){
		vector<F> r(1);
		r[0] = arr[0];
		return r;
	}
	vector<F> l_arr,r_arr;
	vector<F> temp_arr(arr.size()/2);
	for(int i = 0; i < arr.size()/2; i++){
		temp_arr[i] = (arr[i]);
	}
	l_arr = compute_coefficients(temp_arr);
	
	for(int i = 0; i < arr.size()/2; i++){
		temp_arr[i] = (arr[i+arr.size()/2]);
	}
	r_arr = compute_coefficients(temp_arr);
	vector<F> r(2*l_arr.size());
	for(int i = 0; i  < r_arr.size(); i++){
		r[i] = l_arr[i];
	}
	for(int i = 0; i < l_arr.size(); i++){
		r[i+l_arr.size()] = (r_arr[i] - l_arr[i]);
	}
	return r;
}

vector<vector<F>> find_quontents(vector<F> arr, vector<F> x){
	vector<vector<F>> quotients(x.size());
	vector<F> temp;
	for(int i = 0; i < x.size()-1; i++){
		temp = arr_difference(1,1,arr);
		quotients[i] = compute_coefficients(temp);
		arr = arr_difference(x[i],x[i]-F(1),arr);
	}

	vector<F> f = compute_coefficients(arr);

	quotients[x.size()-1].push_back(f[1]);
	return quotients;
}

void generate_pp1(vector<G1> &commitment, vector<F> &beta,G1 G, int idx){
	int size = beta.size()/16;
	int pos = idx*size;
	for(int i = pos; i < pos + size; i++){
		commitment[i] = G*beta[i];
	}
}
void generate_pp2(vector<G2> &commitment, vector<F> &beta,G2 G, int idx){
	int size = beta.size()/16;
	int pos = idx*size;
	for(int i = pos; i < pos + size; i++){
		commitment[i] = G*beta[i];
	}
}


void generate_pp_VC(int bit_size,VC_pp &commitment){
	struct Comm temp_com,temp_com_compressed;
	commitment.bit_size = bit_size;
	
	if(commitment.bit_size%2 == 0){
		commitment.commit_bit_size = commitment.bit_size/2 + offset;
	}else{
		commitment.commit_bit_size = (commitment.bit_size+1)/2 + offset;
	}
	
	generate_pp(temp_com,commitment.commit_bit_size);
	
	commitment.pp1 = temp_com.pp1;
	commitment.pp2 = temp_com.pp2;
	commitment.base = temp_com.base;
	commitment.H = temp_com.H;
	commitment.G = temp_com.G;
	generate_pp(temp_com_compressed,commitment.bit_size-commitment.commit_bit_size);
	commitment.pp1_compressed = temp_com.pp1;
	commitment.pp2_compressed = temp_com.pp2;
	commitment.base_compressed = temp_com.base;
	commitment.H_compressed = temp_com.H;
	commitment.G_compressed = temp_com.G;
	
	vector<G1> temp = commitment.pp1;
	

	commitment.hyper_proofs_base.resize(commitment.commit_bit_size);
	for(int i = 0; i < commitment.commit_bit_size; i++){
		for(int j = 0; j < temp.size()/2; j++){
			commitment.hyper_proofs_base[i].push_back(temp[2*j]+temp[2*j+1]);
		}
		temp = commitment.hyper_proofs_base[i];
	}
	temp = commitment.pp1_compressed;
	commitment.hyper_proofs_base_compressed.resize(commitment.bit_size-commitment.commit_bit_size);
	for(int i = 0; i < commitment.bit_size-commitment.commit_bit_size; i++){
		for(int j = 0; j < temp.size()/2; j++){
			commitment.hyper_proofs_base_compressed[i].push_back(temp[2*j]+temp[2*j+1]);
		}
		temp = commitment.hyper_proofs_base_compressed[i];
	}

	commitment.w.resize(1<<(commitment.bit_size- commitment.commit_bit_size ));
	commitment.u.resize(1<<(commitment.bit_size- commitment.commit_bit_size ));
	thread worker[16];
	vector<F> base;
	for(int i = 0; i < commitment.w.size(); i++){
		base.push_back(F(1+i));
	}
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp1,ref(commitment.w),ref(base),commitment.G,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp2,ref(commitment.u),ref(base),commitment.H,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}



}

void generate_pp_hyperproofs(struct Comm &commitment,int bit_size){
	vector<F> random_values;
	//commitment.H = mcl::bn::getG2basePoint();
	char rand[256];
	for(int i = 0; i < 256; i++){
		rand[i] = i+'4';
	}
	
	//commitment.G = mcl::bn::getG1basePoint();
	mcl::bn::hashAndMapToG1(commitment.G,rand,256);

	mcl::bn::hashAndMapToG2(commitment.H,rand,256);
	commitment.bit_size = bit_size;
	for(int i = 0; i < commitment.bit_size; i++){
		F temp;
		temp.setByCSPRNG();
		random_values.push_back(temp);
	}
	commitment.secret = random_values;
	vector<F> betas,betas2;
	precompute_beta(random_values,betas2);
	compute_binary(random_values, betas);

	thread worker[16];
	commitment.pp1.resize(betas.size());
	
	//for(int i = 0; i < betas.size(); i++){
	//	commitment.pp1[i] = commitment.G*betas[i];
	//}
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp1,ref(commitment.pp1),ref(betas2),commitment.G,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}


	vector<G1> temp = commitment.pp1;
	

	commitment.base.resize(random_values.size());
	for(int i = 0; i < random_values.size(); i++){
		for(int j = 0; j < temp.size()/2; j++){
			commitment.base[i].push_back(temp[2*j]+temp[2*j+1]);
			//commitment.base[i].push_back(temp[2*j]);
		}
		temp = commitment.base[i];
	}

	
	for(int i = 0; i < random_values.size(); i++){
		commitment.pp2.push_back(commitment.H * random_values[i]);
	}
}



void generate_pp(struct Comm &commitment,int bit_size){
	vector<F> random_values;
	//commitment.H = mcl::bn::getG2basePoint();
	char rand[256];
	for(int i = 0; i < 256; i++){
		rand[i] = i+'4';
	}
	
	//commitment.G = mcl::bn::getG1basePoint();
	
	mcl::bn::hashAndMapToG1(commitment.G,"0",1);
	mcl::bn::hashAndMapToG2(commitment.H,rand,256);
	commitment.bit_size = bit_size;
	for(int i = 0; i < commitment.bit_size; i++){
		F temp;
		temp.setByCSPRNG();
		random_values.push_back(temp);
	}
	commitment.secret = random_values;
	vector<F> betas,betas2;
	precompute_beta(random_values,betas2);
	compute_binary(random_values, betas);

	thread worker[16];
	commitment.pp1.resize(betas.size());
	
	//for(int i = 0; i < betas.size(); i++){
	//	commitment.pp1[i] = commitment.G*betas[i];
	//}
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp1,ref(commitment.pp1),ref(betas2),commitment.G,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}


	vector<G1> temp(betas2.size());
	
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp1,ref(temp),ref(betas),commitment.G,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}

	commitment.base.resize(random_values.size());
	for(int i = 0; i < random_values.size(); i++){
		for(int j = 0; j < temp.size()/2; j++){
		//	commitment.base[i].push_back(temp[2*j]+temp[2*j+1]);
			commitment.base[i].push_back(temp[2*j]);
		}
		temp = commitment.base[i];
	}
	
	int idx = 1;
	for(int i = 0; i < random_values.size(); i++){
		commitment.pp2.push_back(commitment.H * betas[idx]);
		idx = idx*2;
	}
}

void generate_pp_vesta(struct Vesta_Comm &commitment,int bit_size){
	int levels = 1;
	int bit = bit_size;
	vector<int> bits,hbits;
	bits.push_back(bit_size);
	hbits.push_back(bit_size-16);
	while(true){
		if(bit == 8){
			bits.push_back(bit);
			hbits.push_back(bit);
			break;
		}
		if(bit > 16){
			bits.push_back(16);
			hbits.push_back(8);
			bit = 8;
		}
		else{
			bits.push_back(bit);
			hbits.push_back(bit/2);
			bit = bit/2;
		}
	}

	for(int i = 0; i < bits.size(); i++){
		printf("%d,%d\n",bits[i],hbits[i] );
	}
	commitment.comm.resize(bits.size());
	commitment.aux_comm.resize(bits.size());
	for(int i = 0; i < commitment.comm.size(); i++){
		generate_pp(commitment.comm[i],bits[i]);
	}

	for(int i = 0; i < commitment.comm.size(); i++){
		generate_pp_hyperproofs(commitment.aux_comm[i],hbits[i]);
	}
	commitment.commitments.resize(bits.size());
}

void commit(vector<F> poly, struct Comm &commitment){
	clock_t start,end;
	start = clock();
	G1::mulVec(commitment.C, commitment.pp1.data(), poly.data(), poly.size());
	end = clock();
	//printf("%lf\n",(float)(end-start)/(float)CLOCKS_PER_SEC );
	
}


void verify_proof(vector<F> x, vector<G2> &pp2,G2 H, vector<G1> &Proof){
	clock_t start,end;
	start = clock();
	vector<G2> diff;
	GT Pairing_prod;

	for(int i = 0; i < x.size(); i++){
		diff.push_back(pp2[i] + H*(F(0)-x[i]));

	}
	end = clock();
	mcl::bn::millerLoopVec(Pairing_prod,Proof.data(),diff.data(),x.size()+1);
	finalExp(Pairing_prod,Pairing_prod);
	vt += (float)(end-start)/(float)CLOCKS_PER_SEC;
}

void open(vector<F> poly, vector<F> x, vector<vector<G1>> &pp, vector<G1> &Proof){
	clock_t start,end;
	vector<vector<F>> quotients = find_quontents(poly,x);
	for(int i = 0; i < x.size(); i++){
		G1 P;
		G1::mulVec(P, pp[i].data(),quotients[i].data(), quotients[i].size());	
		Proof.push_back(P);
	}
	
}

void verify(vector<F> x, F y, struct Comm &commitment){
	
	GT check_P,Pairing_prod;
	vector<G2> diff;
	vector<G1> proofs;
	G1 test = commitment.G*y;

	for(int i = 0; i < x.size(); i++){
		test = test + commitment.Proof[i]*commitment.secret[i];
		proofs.push_back(commitment.Proof[i]);
		diff.push_back(commitment.pp2[i] + commitment.H*(F(0)-x[i]));
	}
	test = test + commitment.C*(F(-1));
	diff.push_back(commitment.H);
	proofs.push_back(commitment.C*(F(-1))+commitment.G*y);
	mcl::bn::millerLoopVec(Pairing_prod,proofs.data(),diff.data(),x.size()+1);
	

	finalExp(Pairing_prod,Pairing_prod);

	if((Pairing_prod).isOne() != 1){
		printf("Error in open\n");
		exit(-1);
	}
}

void _compute_GT_commitment(vector<G1> &x, vector<G2> &y,GT &res, int idx){
	int size = x.size()/threads;
	int pos = idx*size;
	G1 *g = (G1 *)malloc(size*sizeof(G1));
	G2 *p = (G2 *)malloc(size*sizeof(G2));
	
	for(int i = 0; i < size; i++){
		g[i] = x[pos+i];
		p[i] = y[pos+i];
	}
	mcl::bn::millerLoopVec(res, g,p, size);
}


GT compute_pairing_commitment(vector<G1> &x, vector<G2> &ck){
	GT res;

	if(threads == 1 || x.size() <= 4*threads){
		mcl::bn::millerLoopVec(res,x.data(),ck.data(),ck.size());
	}else{
		

		GT _res[threads];
		thread workers[threads];
		for(int i = 0; i < threads; i++){
			workers[i] =  thread(&_compute_GT_commitment,ref(x),ref(ck),ref(_res[i]),i);
		}
		for(int i = 0; i < threads; i++){
			workers[i].join();
		}
		res = _res[0];
		for(int i = 1; i < threads; i++){
			res = res + _res[i];
		}
	
	}
	return res;
}

void _compute_G1_commitment(vector<G1> &ck, vector<F> &x,G1 &res, int idx){
	int size = ck.size()/threads;
	int pos = idx*size;
	G1 *g = (G1 *)malloc(size*sizeof(G1));
	F *p = (F *)malloc(size*sizeof(F));
	for(int i = 0; i < size; i++){
		g[i] = ck[pos+i];
		p[i] = x[pos+i];
	}
	G1::mulVec(res, g,p, size);
}

G1 compute_G1_commitment( vector<G1> &ck,vector<F> &x){
	G1 res;
	if(threads == 1 || x.size() <= 4*threads){
		G1::mulVec(res, ck.data(),x.data(), x.size());
	}else{
		
		G1 _res[threads];
		thread workers[threads];
		for(int i = 0; i < threads; i++){
			workers[i] =  thread(&_compute_G1_commitment,ref(ck),ref(x),ref(_res[i]),i);
		}
		for(int i = 0; i < threads; i++){
			workers[i].join();
		}
		res = _res[0];
		for(int i = 1; i < threads; i++){
			res = res + _res[i];
		}

	}
	return res;	
}


void _base_compute(vector<G1> &A,vector<G1> &A_L,vector<G1> &A_R,vector<G2> &u,vector<G2> &u_l,vector<G2> &u_r,vector<F> &b,vector<F> &B_L,vector<F> &B_R,vector<G1> &w,vector<G1> &w_l,vector<G1> &w_r, F x, F x_inv,int idx){
	int size = A.size()/threads;
	int pos = idx*size;
	for(int j = pos; j < pos+size; j++){
		A[j] = (A_L[j] + A_R[j]*x);
		u[j] = (u_l[j] + u_r[j]*x_inv);
		b[j] = (B_L[j] + B_R[j]*x_inv);
		w[j] = (w_l[j] + w_r[j]*x);
	}
}

void MIPP(vector<G1> A, vector<G2> u,vector<F> b, vector<G1> w, GT T, G1 U, G1 B, G2 h1, G2 h2){
	vector<MIPP_Proof> Proof;
	GT temp_T;
	mcl::bn::millerLoop(temp_T,U,h1);
	T = T + temp_T;
	mcl::bn::millerLoop(temp_T,B,h2);
	T = T + temp_T;
	
	int iter = (int)log2(A.size());
	
	for(int i = 0; i < iter; i++){
		MIPP_Proof P;
		vector<G1> A_L(A.size()/2),A_R(A.size()/2);
		vector<F> B_L(A.size()/2),B_R(A.size()/2);
		vector<G2> u_l(A.size()/2),u_r(A.size()/2);
		vector<G1> w_l(A.size()/2),w_r(A.size()/2);
		for(int j = 0; j < A.size()/2; j++){
			A_L[j] = A[j];
			A_R[j] = A[j+A.size()/2];
			B_L[j] = b[j];
			B_R[j] = b[j+A.size()/2];
			u_l[j] = u[j];
			u_r[j] = u[j+A.size()/2];
			w_l[j] = w[j];
			w_r[j] = w[j+A.size()/2];
		}
		// Send to the verifier
		P.Z_L = compute_G1_commitment(A_R,B_L);
		P.Z_R = compute_G1_commitment(A_L,B_R);
		
		P.G_L = compute_G1_commitment(w_r,B_L);
		P.G_R = compute_G1_commitment(w_l,B_R);
		P.GT_L = compute_pairing_commitment(A_L,u_r);
		P.GT_R = compute_pairing_commitment(A_R,u_l);
		comm_size += 2*sizeof(P.GT_L);
		comm_size += 4*sizeof(P.G_L);

		F x,x_inv;
		x.setByCSPRNG();
		x_inv.inv(x_inv,x); 
		P.x = x;
		P.x_inv = x_inv;
		Proof.push_back(P);
		if(x_inv*x != F(1)){
			printf("Error \n");
			exit(-1);
		}
		// Reduce vectors
		A.resize(A_L.size());
		u.resize(A_L.size());
		b.resize(A_L.size());
		w.resize(A_L.size());
		if(threads == 1 || A_L.size() <= threads){
			for(int j = 0; j < A_L.size(); j++){
				A[j] = (A_L[j] + A_R[j]*x);
				u[j] = (u_l[j] + u_r[j]*x_inv);
				b[j] = (B_L[j] + B_R[j]*x_inv);
				w[j] = (w_l[j] + w_r[j]*x);
			}			
		}else{
			thread workers[threads];
			for(int j = 0; j < threads; j++){
				workers[j] = thread(&_base_compute,ref(A),ref(A_L),ref(A_R),ref(u),ref(u_l),ref(u_r),ref(b),ref(B_L),ref(B_R),ref(w),ref(w_l),ref(w_r),x,x_inv,j);
			}
			for(int j = 0; j < threads; j++){
				workers[j].join();
			}

		}
	}
	
	G1 C_g1 = U;
	GT C_gt = T;
	G1 C_inner = B;
	clock_t s1,s2;
	s1 = clock();
	for(int i = 0; i < iter; i++){
		C_g1 = Proof[i].G_L*Proof[i].x + C_g1 + Proof[i].G_R*Proof[i].x_inv;
		//C_gt = Proof[i].GT_L*Proof[i].x + C_gt + Proof[i].GT_R*Proof[i].x_inv;
		C_inner = Proof[i].Z_L*Proof[i].x + C_inner + Proof[i].Z_R*Proof[i].x_inv;
	}
	G1 final_inner = A[0]*b[0];
	s2 = clock();
	vt += (double)(s2 - s1)/(double)CLOCKS_PER_SEC;
	/*if(final_inner != C_inner){
		printf("Error in MIPP\n");
		exit(-1);
	}
	*/
	
}


void test_MIPP(){
	int size = 1024*16;
	vector<G1> ck1,A;
	vector<F> B;
	vector<G2> ck2;
	char rand[256];
	G2 h;
	mcl::bn::hashAndMapToG2(h,rand,256);
	G1 g = mcl::bn::getG1basePoint();

	for(int i = 0; i < size; i++){
		F num;
		num.setByCSPRNG();
		B.push_back(num);
		ck1.push_back(g*num);
		A.push_back(g*(num+num));
		ck2.push_back(h*num); 
	}
	MIPP(A,ck2,B,ck1,compute_pairing_commitment(A,ck2),compute_G1_commitment(ck1,B),compute_G1_commitment(A,B),h,h);

}

void copy_pp(MIPP_Comm &commitment1,MIPP_Comm &commitment2){
	commitment2.bit_size = commitment1.bit_size;
	commitment2.commit_bit_size = commitment1.commit_bit_size;
	commitment2.pp1 = commitment1.pp1;
	commitment2.pp2 =commitment1.pp2;
	commitment2.base = commitment1.base;
	commitment2.precompute = commitment1.precompute;
	commitment2.H = commitment1.H ;
	commitment2.G = commitment1.G ;
	commitment2.bits = commitment1.bits ;
	commitment2.w = commitment1.w;
	commitment2.u = commitment1.u;
	commitment2.precomputed_pp = commitment1.precomputed_pp;
}

void MIPP_gen(int bit_size,MIPP_Comm &commitment, bool precompute,bool bits){
	struct Comm temp_com;
	commitment.bit_size = bit_size;
	if(!bits){

		if(commitment.bit_size%2 == 0){
			commitment.commit_bit_size = commitment.bit_size/2 + 2 ;
		}else{
			commitment.commit_bit_size = (commitment.bit_size+1)/2 + 2;
		}
	}else{
		if(commitment.bit_size%2 == 0){
			commitment.commit_bit_size = commitment.bit_size/2 + 3;
		}else{
			commitment.commit_bit_size = (commitment.bit_size+1)/2 + 3;
		}
	}

	if(precompute && bits){
		commitment.commit_bit_size = commitment.bit_size;
	}
	generate_pp(temp_com,commitment.commit_bit_size);
	
	commitment.pp1 = temp_com.pp1;
	commitment.pp2 = temp_com.pp2;
	commitment.base = temp_com.base;
	commitment.precompute = precompute;
	commitment.H = temp_com.H;
	commitment.G = temp_com.G;
	commitment.bits = bits;

	commitment.w.resize(1<<(commitment.bit_size- commitment.commit_bit_size ));
	commitment.u.resize(1<<(commitment.bit_size- commitment.commit_bit_size ));
	thread worker[16];
	vector<F> base;
	for(int i = 0; i < commitment.w.size(); i++){
		base.push_back(F(1+i));
	}
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp1,ref(commitment.w),ref(base),commitment.G,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp2,ref(commitment.u),ref(base),commitment.H,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}
	//for(int i = 0; i < 1<<(commitment.bit_size- commitment.commit_bit_size ); i++){
	//	commitment.w.push_back(commitment.G*F(1+i));
	//	commitment.u.push_back(commitment.H*F(1+i));
	//}

	if(precompute && bits == false){
		vector<vector<G1>> precomputed_pp(255);
		if(Q == 16){
			precomputed_pp.resize(510);
		}
		precomputed_pp[0] = commitment.pp1;
		for(int i = 1; i < 255; i++){
			for(int j = 0; j < precomputed_pp[i-1].size(); j++){
				precomputed_pp[i].push_back(precomputed_pp[i-1][j] + precomputed_pp[0][j]);
			}
		}
		if(Q == 16){
			for(int i = 255; i < 510; i++){
				for(int j = 0; j < precomputed_pp[0].size(); j++){
					precomputed_pp[i].push_back(precomputed_pp[i-1][j] + precomputed_pp[254][j]);
				}
			}
		}
		commitment.precomputed_pp = precomputed_pp;
	}


}


void MIPP_fold_commit(vector<F> f1, vector<F> bits, MIPP_Comm &commitment){
	int size = 1<<(commitment.commit_bit_size);
	

	for(int i = 0; i < 1<< (commitment.bit_size - commitment.commit_bit_size); i++){
		vector<F> exp;
		unordered_map<F,int> table;
		int counter = 0;
		vector<F> arr(size);
		vector<F> elements;
		G1 C;
		for(int j = 0; j < size; j++){
			arr[j] = f1[i*size + j];
		}
	
		for(int j = 0; j < size; j++){
			if(f1[j] == F(0) || bits[i*size + j] == F(0)) continue;
			if(table.find(f1[j]) == table.end()){
				table[f1[j]] = counter++;
				elements.push_back(f1[j]);
			}
		}
		vector<G1> bases;
		for(int i = 0; i < elements.size(); i++){
			bases.push_back(commitment.G*F(0));
		}
	
		for(int j = 0; j < size; j++){
			if(f1[j] == F(0) || bits[i*size + j] == F(0)) continue;
	
			int idx = table[f1[j]];
			bases[idx] = bases[idx] + commitment.pp1[j];
			
		}
		printf("%d\n",bases.size() );
		commitment.Commitments.push_back(compute_G1_commitment(bases,elements));
	}
	//commitment.C_T = compute_pairing_commitment(commitment.Commitments,commitment.u);
}


void _MIPP_predicate_commit(vector<int> &mapping, MIPP_Comm &commitment, vector<G1> &commitments,int threads , int idx){
	int L = (1<<(commitment.bit_size - commitment.commit_bit_size))/threads;
	int pos = L*idx;
	int size = 1<<(commitment.commit_bit_size-8);
	vector<int> arr(size);
	for(int i = pos; i < pos + L; i++){
		G1 C = commitment.G*F(0);
		for(int j = 0; j  < size; j++){
			arr[j] = mapping[i*size + j];
		}
		for(int j = 0; j < size; j++){
			C = C + commitment.pp1[256*j + arr[j]];
		}
		commitments.push_back(C);
	}
}


void MIPP_predicate_commit(vector<int> &mapping, MIPP_Comm &commitment){
	auto s = high_resolution_clock::now();


	int size = 1<<(commitment.commit_bit_size-8);
	if(threads == 1){
		vector<int> arr(size);
		int counter = 0;
		for(int i = 0; i <  1<<(commitment.bit_size - commitment.commit_bit_size); i++){
			G1 C = commitment.G*F(0);
			for(int j = 0; j  < size; j++){
				arr[j] = mapping[i*size + j];
			}
			for(int j = 0; j < size; j++){
				C = C + commitment.pp1[256*j + arr[j]];
				counter += 1;
			}
			commitment.Commitments.push_back(C);
		}
	}else{
		int _threads = threads;
		if(_threads <  1<<(commitment.bit_size - commitment.commit_bit_size)){
			_threads = 1<<(commitment.bit_size - commitment.commit_bit_size);
		}
		thread workers[_threads];
		vector<vector<G1>> commitments(_threads);
		for(int i = 0; i < _threads; i++){
			workers[i] = thread(&_MIPP_predicate_commit,ref(mapping),ref(commitment),ref(commitments[i]),_threads,i);
		}
		for(int i = 0; i < _threads; i++){
			workers[i].join();
		}
		for(int i = 0; i < _threads; i++){
			for(int j = 0; j < commitments[i].size(); j++){
				commitment.Commitments.push_back(commitments[i][j]);
			}
		}
	}
	commitment.C_T = compute_pairing_commitment(commitment.Commitments,commitment.u);
	comm_size += sizeof(commitment.C_T);
	
	auto e = high_resolution_clock::now();
	auto d = duration_cast<microseconds>(e - s);
	printf("(%lf)\n",d.count()/1000000.0 );
}


void _MIPP_commit( vector<F> &poly,vector<int> &poly_int , MIPP_Comm &commitment, vector<G1> &commitments,int threads , int idx){
	
	int L = (1<<(commitment.bit_size - commitment.commit_bit_size))/threads;
	int pos = L*idx;
	
	int size = 1<<(commitment.commit_bit_size);
	if(commitment.bits){
		vector<F> arr(size);
		for(int i = pos; i < pos+L; i++){
			G1 C = commitment.G*F(0);
			for(int j = 0; j < size; j++){
				arr[j] = poly[i*size + j];
			}
			for(int j = 0; j < size; j++){
				if(arr[j] == 0){
					continue;
				}
				else{
					C = C + commitment.pp1[j];
				}
			}
			commitments.push_back(C);
		}
	}else{
		vector<int> arr(size);
		for(int i = pos; i < pos+L; i++){
			G1 C = commitment.G*F(0);
			for(int j = 0; j < size; j++){
				arr[j] = poly_int[i*size + j];
			}
			for(int j = 0; j < size; j++){
				if(arr[j] == 0){
					continue;
				}
				if(arr[j]/256 == 0){
					C = C + commitment.precomputed_pp[arr[j]-1][j];
				}else{
					C = C + commitment.precomputed_pp[254 + arr[j]/256][j];
					if(arr[j]%256 != 0){
						C = C + commitment.precomputed_pp[arr[j]%256-1][j];
					}
				}
			}
			commitments.push_back(C);
		}	
	}
}

void MIPP_commit(vector<F> &poly,vector<int> &poly_int, MIPP_Comm &commitment){
	auto s = high_resolution_clock::now();

	int size = 1<<(commitment.commit_bit_size);
	//printf("%d,%d\n",size,  1<<(commitment.bit_size - commitment.commit_bit_size));
	if(!commitment.precompute && !commitment.bits){
		vector<F> arr(size);
		//printf("Comms : %d, size : %d\n",1<<(commitment.bit_size - commitment.commit_bit_size),size );
		for(int i = 0; i < 1<<(commitment.bit_size - commitment.commit_bit_size); i++){
			for(int j = 0; j < size; j++){
				arr[j] = poly[i*size + j];
			}
			commitment.Commitments.push_back(compute_G1_commitment(commitment.pp1,arr));
		}
	}else{
		if(threads == 1){
			if(commitment.bits){
				vector<F> arr(size);
				int counter =0;
				for(int i = 0; i < 1<<(commitment.bit_size - commitment.commit_bit_size); i++){
					G1 C = commitment.G*F(0);
					for(int j = 0; j < size; j++){
						arr[j] = poly[i*size + j];
					}
					for(int j = 0; j < size; j++){
						if(arr[j] == 0){
							continue;
						}
						else{
							C = C + commitment.pp1[j];
							counter++;
						}
					}
					commitment.Commitments.push_back(C);
				}
				//printf("%d,%d\n",counter, 1<<commitment.bit_size);
			}
			else{
				vector<int> arr(size);
				for(int i = 0; i < 1<<(commitment.bit_size - commitment.commit_bit_size); i++){
					G1 C = commitment.G*F(0);
					for(int j = 0; j < size; j++){
						arr[j] = poly_int[i*size + j];
					}
					for(int j = 0; j < size; j++){
						if(arr[j] == 0){
							continue;
						}
						if(arr[j]/256 == 0){
							C = C + commitment.precomputed_pp[arr[j]-1][j];
						}else{
							C = C + commitment.precomputed_pp[254 + arr[j]/256][j];
							if(arr[j]%256 != 0){
								C = C + commitment.precomputed_pp[arr[j]%256-1][j];
							}
						}
					}
					commitment.Commitments.push_back(C);
				}	
			}
		}else{
			int _threads = threads;
			if(_threads >  1<<(commitment.bit_size - commitment.commit_bit_size)){
				_threads = 1<<(commitment.bit_size - commitment.commit_bit_size);
			}
			
			thread workers[_threads];
			vector<vector<G1>> commitments(_threads);
			for(int i = 0; i < _threads; i++){
				workers[i] = thread(&_MIPP_commit,ref(poly),ref(poly_int),ref(commitment),ref(commitments[i]),_threads,i);
			}
			
			for(int i = 0; i < _threads; i++){
				workers[i].join();
			}
			for(int i = 0; i < _threads; i++){
				for(int j = 0; j < commitments[i].size(); j++){
					commitment.Commitments.push_back(commitments[i][j]);
				}
			}
		}
	}
	
	commitment.C_T = compute_pairing_commitment(commitment.Commitments,commitment.u);
	comm_size += sizeof(commitment.C_T);
	
	auto e = high_resolution_clock::now();
	auto d = duration_cast<microseconds>(e - s);
	
}

void MIPP_predicate_open(vector<int> mapping, vector<F> x, MIPP_Comm &commitment){
	vector<F> r1,r2;
	for(int i = 0; i < commitment.bit_size - commitment.commit_bit_size; i++){
		r1.push_back(x[i]);
	}
	for(int i = commitment.bit_size - commitment.commit_bit_size; i < commitment.bit_size; i++){
		r2.push_back(x[i]);
	}
	

	vector<F> aggr_poly(1 << commitment.commit_bit_size,F(0));
	auto s = high_resolution_clock::now();
	vector<F> betas;
	precompute_beta(r1,betas);
	int size = 1<<(commitment.commit_bit_size-8);

	for(int i = 0; i < 1<<(commitment.bit_size - commitment.commit_bit_size); i++){
		for(int j = 0; j < size; j++){
			aggr_poly[256*j + mapping[j]] += betas[i];
		}	
	}
	// Prepare commitments for MIPP
	
	G1 Agg_C = compute_G1_commitment(commitment.Commitments,betas);
	G1 P = compute_G1_commitment(commitment.w,betas);
	
	
	
	MIPP(commitment.Commitments,commitment.u,betas,commitment.w,commitment.C_T,P,Agg_C,commitment.H,commitment.H);
	commitment.Agg_C = Agg_C;
	commitment.r2 = r2;
	// Open aggregated polynomial
	
	
	vector<vector<F>> quotients = find_quontents(aggr_poly,r2);
	
	for(int i = 0; i < r2.size(); i++){
		G1 P;
		P = compute_G1_commitment(commitment.base[i],quotients[i]);
		//G1::mulVec(P, commitment.base[i].data(),quotients[i].data(), quotients[i].size());	
		commitment.Proof.push_back(P);
	}
	
	auto e = high_resolution_clock::now();
	auto d = duration_cast<microseconds>(e - s);
	comm_size += sizeof(commitment.Proof[0])*r2.size();
	printf("(%lf)\n",d.count()/1000000.0 );

}

void _aggregate(vector<F> &aggr_poly,vector<F> &betas,vector<F> &poly,int L,int L2, int idx){
	int size = L/threads;
	int pos = size*idx;
	for(int i = 0; i < L2; i++){
		for(int j = pos; j < pos + size; j++){
			aggr_poly[j] += betas[i]*poly[i*L+j];
		}
	}
}

void MIPP_open(vector<F> poly,vector<F> x, MIPP_Comm &commitment){
	vector<F> r1,r2;
	for(int i = 0; i < commitment.bit_size - commitment.commit_bit_size; i++){
		r1.push_back(x[i + commitment.commit_bit_size]);
	}
	for(int i = commitment.bit_size - commitment.commit_bit_size; i < commitment.bit_size; i++){
		r2.push_back(x[i - (commitment.bit_size - commitment.commit_bit_size)]);
	}
	vector<F> aggr_poly(1 << commitment.commit_bit_size,F(0));
	auto s = high_resolution_clock::now();

	
	vector<F> betas;
	precompute_beta(r1,betas);
	int size = 1<<(commitment.commit_bit_size);
	// Aggregate polynomials
	if(threads == 1){
		for(int i = 0; i < 1<<(commitment.bit_size - commitment.commit_bit_size); i++){
			for(int j = 0; j < size; j++){
				aggr_poly[j] += betas[i]*poly[i*size + j];
			}
		}
	}else{
		thread workers[threads];
		for(int i = 0; i < threads; i++){
			workers[i] = thread(_aggregate,ref(aggr_poly),ref(betas),ref(poly),size,1<<(commitment.bit_size - commitment.commit_bit_size),i);
		}
		for(int i = 0; i < threads; i++){
			workers[i].join();
		}
	}
	
	// Prepare commitments for MIPP
	printf("%d,%d\n",commitment.Commitments.size(),betas.size());
	G1 Agg_C = compute_G1_commitment(commitment.Commitments,betas);
	G1 P = compute_G1_commitment(commitment.w,betas);
	
	MIPP(commitment.Commitments,commitment.u,betas,commitment.w,commitment.C_T,P,Agg_C,commitment.H,commitment.H);
	commitment.Agg_C = Agg_C;
	commitment.r2 = r2;
	// Open aggregated polynomial
	
	vector<vector<F>> quotients = find_quontents(aggr_poly,r2);
	
	for(int i = 0; i < r2.size(); i++){
		G1 P;
		P = compute_G1_commitment(commitment.base[i],quotients[i]);
		//G1::mulVec(P, commitment.base[i].data(),quotients[i].data(), quotients[i].size());	
		commitment.Proof.push_back(P);
	}


	auto e = high_resolution_clock::now();
	auto d = duration_cast<microseconds>(e - s);
	printf("(%lf)\n",d.count()/1000000.0 );


}

void MIPP_verify( F y, MIPP_Comm &commitment){
	
	GT check_P,Pairing_prod;
	vector<G2> diff;
	vector<G1> proofs;
	
	auto s = high_resolution_clock::now();

	for(int i = 0; i < commitment.r2.size(); i++){
		proofs.push_back(commitment.Proof[i]);
		diff.push_back(commitment.pp2[i] + commitment.H*(F(0)-commitment.r2[i]));
	}
	diff.push_back(commitment.H);
	proofs.push_back(commitment.Agg_C*(F(-1))+commitment.G*y);
	mcl::bn::millerLoopVec(Pairing_prod,proofs.data(),diff.data(),commitment.r2.size()+1);
	
	comm_size += proofs.size()*sizeof(commitment.G);
	
	finalExp(Pairing_prod,Pairing_prod);
	auto e = high_resolution_clock::now();
	auto d = duration_cast<microseconds>(e - s);
	verification_time += d.count()/1000000.0;
	vt += d.count()/1000000.0;
	if((Pairing_prod).isOne() != 1){
		//printf("Error in open\n");
		//exit(-1);
	}

}



vector<vector<F>> segment(vector<F> &poly,int bits){
	vector<vector<F>> partitions(1<<(bits/2));
	for(int i = 0; i < 1<<(bits/2); i++){
		partitions[i].resize(partitions.size());
		for(int j = 0; j < partitions[i].size(); j++){
			partitions[i][j] = poly[i*(1<<(bits/2)) + j];
		}
	}
	return partitions;
}

vector<G1> compute_commitments(vector<vector<F>> &partitions, vector<G1> &pp){
	vector<G1> Commitments(partitions.size());
	
	for(int i = 0; i < partitions.size(); i++){
		G1::mulVec(Commitments[i], pp.data(), partitions[i].data(), partitions[i].size());
	}
	return Commitments;
}


void Vesta_Commit(vector<F> poly, Vesta_Comm &commitment, int level){
	int bits = (int)log2(poly.size());
	if(bits == 8){
		return;
	}
	else if(bits > 16){
		vector<vector<F>> partitions(poly.size()/(1<<16));
		for(int i = 0; i < partitions.size(); i++){
			partitions[i].resize(1<<16);
			for(int j = 0; j < 1<<16; j++){
				partitions[i][j] = poly[i*(1<<16) + j];
			}
			G1 C;
			//printf("%d,%d\n", commitment.comm[level+1].pp1.size(),partitions[i].size());
			G1::mulVec(C,commitment.comm[level+1].pp1.data(),partitions[i].data(),1<<16);
			commitment.commitments[level+1].push_back(C);
		}
		for(int i = 0; i < partitions.size(); i++){
			Vesta_Commit(partitions[i],commitment,level+1);
		}
	}else{
		vector<vector<F>> partitions = segment(poly,bits);
		for(int i = 0; i < partitions.size(); i++){
			G1 C;
			G1::mulVec(C,commitment.comm[level+1].pp1.data(),partitions[i].data(),partitions[i].size());
			commitment.commitments[level+1].push_back(C);
		}
		for(int i = 0; i < partitions.size(); i++){
			Vesta_Commit(partitions[i],commitment,level+1);
		}
	}
}
/*
void VestaOpenAll(vector<F> poly){
	int bits = (int)log2(poly.size());
	Comm comm,poly_comm;
	vector<G1> partial_commitments;
	
	vector<F> eval_point(bits/2);

	generate_pp(comm,bits/2);
	generate_pp(poly_comm,bits);
	printf("PP generated\n");
	clock_t s,e;
	s = clock();
	commit(poly,poly_comm);
	for(int i = 0; i < eval_point.size(); i++){
		eval_point[i].setByCSPRNG();
	}

	vector<vector<F>> partitions = segment(poly,bits);
	vector<F> evaluations_vector(1<<(bits/2));
	for(int i = 0; i < evaluations_vector.size(); i++){
		evaluations_vector[i] = evaluate_vector(partitions[i],eval_point);
	}
	clock_t ts;
	ts = clock();
	partial_commitments = compute_commitments(partitions,comm.pp1);
	clock_t te;
	te = clock();
	printf("Commitment : %lf\n",(float)(te - ts)/(float)CLOCKS_PER_SEC );
	vector<vector<F>> chalenge_points(bits/2);
	vector<vector<G1>> aggregated_commitments(bits/2+1);
	vector<vector<vector<F>>> partitions_placeholder(bits/2+1);
	vector<vector<F>> evaluations(bits/2+1);
	evaluations[0] = evaluations_vector;
	partitions_placeholder[0] = partitions;
	aggregated_commitments[0] = partial_commitments;
	int L;
	
	for(int i = 0; i < bits/2; i++){
		L = 1<<(bits/2 - 1 - i);
		vector<F> temp_poly(partitions_placeholder[i][0].size());
		for(int j = 0; j < L; j++){
			F c1,c2;
			c1.setByCSPRNG();
			c2.setByCSPRNG();
			chalenge_points[i].push_back(c1);
			chalenge_points[i].push_back(c2);
			evaluations[i+1].push_back(c1*evaluations[i][2*j] + c2*evaluations[i][2*j+1]);
			aggregated_commitments[i+1].push_back(aggregated_commitments[i][2*j]*c1 + aggregated_commitments[i][2*j+1]*c2);
			
			for(int k = 0; k < temp_poly.size(); k++){
				temp_poly[k] = c1*partitions_placeholder[i][2*j][k] + c2*partitions_placeholder[i][2*j+1][k];
			}
			partitions_placeholder[i+1].push_back(temp_poly); 
		}
	}
	vector<F> final_poly = partitions_placeholder[bits/2][0];
	if(evaluate_vector(final_poly,eval_point) != evaluations[bits/2][0]){
		printf("Error in folding scheme\n");
		exit(-1);
	}
	open(final_poly,eval_point,comm);
	hyperproofs_openall(final_poly,comm);
	hyperproofs_openall(evaluations_vector,comm);
	vector<F> eval_point2(bits/2);
	vector<F> eval = eval_point; 
	for(int i = 0; i < bits/2; i++){
		eval_point2[i].setByCSPRNG();
		eval.push_back(eval_point2[i]);
	}
	open(evaluations_vector,eval_point2,comm);
	open(poly,eval,poly_comm);
	e = clock();
	printf("Open All time : %lf\n",(float)(e-s)/(float)CLOCKS_PER_SEC);
}


void Vesta_OpenAll(vector<F> poly, Vesta_Comm &commitment, int level){

	int bits = (int)log2(poly.size());

	if(poly.size() == 2){
		return;
	}
	else if(bits == 8){

		clock_t s,e;
		s = clock();
		hyperproofs_openall(poly,commitment.aux_comm[level]);
		e = clock();
		proving_time += (float)(e-s)/(float)CLOCKS_PER_SEC;
	}
	else if(bits > 16){
		// Partition to 2^16 sized vectors
		vector<F> r1(16),r2(bits-16);
		for(int i = 0; i < r1.size(); i++){
			F num;
			num.setByCSPRNG();
			r1[i] = num;
		}
		for(int i = 0; i < r2.size(); i++){
			F num;
			num.setByCSPRNG();
			r2[i] = num;
		}


		
		clock_t s,e;
		s = clock();
		
		vector<vector<F>> partitions(poly.size()/(1<<16));
		for(int i = 0; i < partitions.size(); i++){
			partitions[i].resize(1<<16);
			for(int j = 0; j < 1<<16; j++){
				partitions[i][j] = poly[i*(1<<16) + j];
			}
		}
		//vector<G1> commitments = compute_commitments(partitions,partitions_comm.pp1);
		vector<F> partial_evaluations(partitions.size());
		
		for(int i = 0; i < partial_evaluations.size(); i++){
			partial_evaluations[i] = evaluate_vector(partitions[i],r1);
		}
		G1 temp_commitment;
		G1::mulVec(temp_commitment, commitment.aux_comm[level].pp1.data(), partial_evaluations.data(), partial_evaluations.size());
		
		for(int i = 0; i < partitions.size(); i++){
			open(partitions[i],r1,commitment.comm[level+1]);
		}
		open(partial_evaluations,r2,commitment.aux_comm[level]);
		vector<vector<G1>> proof_tree((int)log2(partial_evaluations.size()));
		hyperproofs_openall(partial_evaluations,commitment.aux_comm[level]);
		e = clock();
		proving_time += (float)(e-s)/(float)CLOCKS_PER_SEC;
		printf("Time : %lf\n",proving_time);
		for(int i = 0; i < partitions.size(); i++){
			Vesta_OpenAll(partitions[i],commitment,level+1);
		}

	}
	else{

		vector<F> r1(bits/2),r2(bits/2);

		for(int i = 0; i < r1.size(); i++){
			F num;
			num.setByCSPRNG();
			r1[i] = num;
			num.setByCSPRNG();
			r2[i] = num;
		}
		clock_t s,e;
		s = clock();
		vector<vector<F>> partitions = segment(poly,bits);
		//vector<G1> commitments = compute_commitments(partitions,partitions_comm.pp1);
		
		vector<F> partial_evaluations(1<<(bits/2));
		//precompute_beta(r,beta);
		for(int i = 0; i < partial_evaluations.size(); i++){
			partial_evaluations[i] = evaluate_vector(partitions[i],r1);
		}
		G1 temp_commitment;
		G1::mulVec(temp_commitment, commitment.aux_comm[level].pp1.data(), partial_evaluations.data(), partial_evaluations.size());
		
		for(int i = 0; i < partitions.size(); i++){
			open(partitions[i],r1,commitment.comm[level+1]);
		}
		open(partial_evaluations,r2,commitment.aux_comm[level]);
		
		vector<vector<G1>> proof_tree((int)log2(partial_evaluations.size()));
		
		hyperproofs_openall(partial_evaluations,commitment.aux_comm[level]);
		
		e = clock();
		proving_time += (float)(e-s)/(float)CLOCKS_PER_SEC;
		
		printf("time level %d : %lf\n",level, (float)(e-s)/(float)CLOCKS_PER_SEC);
		for(int i = 0; i < partitions.size(); i++){
			Vesta_OpenAll(partitions[i],commitment,level+1);
		}
	}
}

*/
