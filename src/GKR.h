#pragma once

#include "verifier.h"
#include "inputCircuit.hpp"
#include <gmp.h>
#include <stdlib.h>
#include "polynomial.h"
#include "config_pc.hpp"
#include <map>

#define GKR_PROOF 1
#define RANGE_PROOF 2
#define RANGE_PROOF_OPT 6
#define RANGE_PROOF_LOOKUP 7

#define MATMUL_PROOF 3 
#define ADD_PROOF 4
#define DIVISION_CHECK 5




struct proof{
	int type;
	vector<vector<F>> randomness;
	vector<quadratic_poly> q_poly;
	vector<cubic_poly> c_poly;
	
	vector<F> vr;
	vector<F> gr;
	vector<F> liu_sum;
	vector<vector<F>> sig;
	vector<vector<F>> final_claims_v;
	F divident,divisor,quotient,remainder;
	// Witnesses to make hash calclulation circuit less deep
	vector<vector<vector<F>>> w_hashes;
	vector<F> r,individual_sums;
	vector<vector<F>> Partial_sums;
	vector<quadratic_poly> q_poly1;
	vector<quadratic_poly> q_poly2;
	int K;

};

struct polynomial_data{
	vector<F> poly;
	vector<vector<F>> eval_point;
	vector<F> eval;
};

struct feedforward_proof{
	map<string,struct polynomial_data> poly_map;
	vector<struct proof> proofs;
};


typedef struct Point Point;
struct proof generate_GKR_proof(char *circuit_name, char *input_file,vector<F> data,vector<F> randomness, bool debug);
struct proof prove_dx_prod(vector<F> data, vector<F> randomness,int vector_size,int N, int ch_in,int ch_out);
struct proof prove_dw_prod(vector<F> data, vector<F> randomness,int vector_size,int N, int ch_in,int ch_out);
struct proof prove_dot_x_prod(vector<F> data, vector<F> randomness,int vector_size,int N, int ch_in,int ch_out);
struct proof prove_avg_der(vector<F> data, vector<F> randomness,int batch, int chin, int w, int w_pad,int window,int mod);
struct proof prove_relu(vector<F> data, vector<F> randomness,int vector_size);
struct proof prove_avg(vector<F> data, vector<F> randomness,int n_padded, int n, int batch, int chout);

struct proof prove_reduce(vector<F> data, vector<F> randomness, int kernels, int dw, int kernel_size);
struct proof prove_padding(vector<F> data, vector<F> randomness,int N, int c, int w, int dim1,int dim2,int middle);
struct proof prove_flat_backprop(vector<F> data, vector<F> randomness,int batch, int chout, int w, int w_pad);
struct proof prove_flat(vector<F> data, vector<F> randomness,int batch, int chout, int w, int w_final);
struct proof prove_rescaling(vector<F> data, vector<F> randomness,int N, int chout, int w_padded, int w);
struct proof prove_aggregation(vector<F> data, vector<F> randomness,int commitments);
struct proof prove_hash_verification(vector<F> data, vector<F> randomness,vector<vector<int>> transcript);
struct proof prove_verification(vector<F> data, vector<F> randomness,vector<vector<int>> transcript);
struct proof prove_input_commit(vector<F> data, vector<F> randomness, int batch, int N);

struct proof prove_division(vector<F> data, vector<F> randomness, int N, int size);
struct proof prove_lookup_product(vector<F> data, vector<F> randomness, int N);
struct proof prove_lookup_circuit(vector<F> data, vector<F> randomness, int batch, int out);
struct proof prove_correctness(vector<F> data, vector<F> randomness, int N, int size);

struct proof prove_bulletproof_verifier(vector<F> data, vector<F> randomness,int commitments);

struct proof prove_smallness(vector<F> data, vector<F> randomness,int size);

struct proof hadamard_product(vector<F> data, vector<F> randomness, int N);
struct proof pardon_div(vector<F> data, vector<F> randomness, int N, int M);
struct proof check_pardon_div(vector<F> data, vector<F> randomness, int N, int M);
struct proof check_max(vector<F> data, vector<F> randomness, int N, int M);
struct proof sqrt_matrix(vector<F> data, vector<F> randomness, int N);
struct proof sqrt_aux(vector<F> data, vector<F> randomness, int N);
struct proof extract_diagonal(vector<F> data, vector<F> randomness, int N);
struct proof prove_log(vector<F> data, vector<F> randomness, int N);
struct proof prove_inv_relu(vector<F> data, vector<F> randomness, int N);
struct proof range_proof(vector<F> data, vector<F> randomness, int N);