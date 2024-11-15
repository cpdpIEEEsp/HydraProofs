#pragma once

#include "verifier.h"
#include "inputCircuit.hpp"
#include <gmp.h>
#include <stdlib.h>
#include "polynomial.h"
#include "config_pc.hpp"
#include <map>
#include "sumcheck.h"
#define GKR_PROOF 1
#define RANGE_PROOF 2
#define RANGE_PROOF_OPT 6
#define RANGE_PROOF_LOOKUP 7

#define MATMUL_PROOF 3 
#define ADD_PROOF 4
#define DIVISION_CHECK 5





struct proof generate_GKR_proof(char *circuit_name, char *input_file,vector<F> data,vector<F> randomness, bool debug);


struct proof prove_multree(vector<F> data, vector<F> randomness,int input_size);