#pragma once

#include "config_pc.hpp"
#include "polynomial.h"


struct proof{
	int type;
	vector<vector<F>> randomness;
	vector<quadratic_poly> q_poly;
	vector<quadruple_poly> quad_poly;
	vector<cubic_poly> c_poly;
	vector<F> output;
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
	F final_rand;
	F final_sum;
	int K;

};

typedef struct proof proof;

struct proof prove_fft(vector<F> M, vector<F> r, F previous_sum);
struct proof prove_ifft(vector<F> M, vector<F> r, F previous_sum);
struct proof prove_ifft_matrix(vector<vector<F>> M, vector<F> r, F previous_sum);
struct proof prove_fft_matrix(vector<vector<F>> M, vector<F> r, F previous_sum);

vector<proof> mimc_sumcheck(vector<F> input);