#ifndef POLY_COMMIT_H
#define POLY_COMMIT_H

#include "config_pc.hpp"

struct Comm{
	vector<G1> pp1;
	vector<G2> pp2;
	vector<G1> Proof;
	vector<F> secret;
	vector<vector<G1>> base;
	G1 G,C;
	G2 H;
	int bit_size;
};

struct Vesta_Comm{
	vector<struct Comm> comm;
	vector<struct Comm> aux_comm;
	vector<vector<G1>> commitments;
};


struct MIPP_Proof{
	F x,x_inv;
	GT GT_L,GT_R;
	G1 G_L,G_R,Z_L,Z_R;

};
typedef struct MIPP_Proof;


struct MIPP_Comm{
	vector<G1> pp1;
	vector<G2> pp2;
	vector<vector<G1>> precomputed_pp;
	vector<vector<G1>> base;
	vector<G1> Commitments;
	vector<G1> Proof;
	vector<G2> u;
	vector<G1> w;
	vector<F> r2;
	vector<MIPP_Proof> M_Proof;
	G1 G,C,Agg_C;
	G2 H;
	GT C_T;
	int bit_size,commit_bit_size;	
	bool precompute;
	bool bits;
};

typedef struct Vesta_Comm;
typedef struct MIPP_Comm;
typedef struct Comm;

void commit(vector<F> poly,struct Comm &commitment);
void verify(vector<F> x, F y,struct Comm &commitment);
void open(vector<F> poly, vector<F> x, struct Comm &commitment);
void generate_pp(struct Comm &commitment,int bit_size);
void test_MIPP();

void MIPP_commit(vector<F> &poly,vector<int> &poly_int, MIPP_Comm &commitment);
void MIPP_open(vector<F> poly,vector<F> x, MIPP_Comm &commitment);
void MIPP_gen(int bit_size,MIPP_Comm &commitment, bool precompute,bool bits);

void MIPP_verify( F y, MIPP_Comm &commitment);
void MIPP_fold_commit(vector<F> f1, vector<F> bits, MIPP_Comm &commitment);
void MIPP_predicate_commit(vector<int> &mapping, MIPP_Comm &commitment);
void MIPP_predicate_open(vector<int> mapping, vector<F> x, MIPP_Comm &commitment);
void copy_pp(MIPP_Comm &commitment1,MIPP_Comm &commitment2);
void hyperproofs_openall(vector<F> poly,Comm &commitment);
void generate_pp_hyperproofs(struct Comm &commitment,int bit_size);
void Vesta_OpenAll(vector<F> poly, Vesta_Comm &commitment,int level);
void generate_pp_vesta(struct Vesta_Comm &commitment,int bit_size);
void Vesta_Commit(vector<F> poly, Vesta_Comm &commitment, int level);
void VestaOpenAll(vector<F> poly);
#endif