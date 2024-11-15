#include "config_pc.hpp"
#include "GKR.h"

proof verify_hashes(vector<struct proof> P);
void verify_gkr(struct proof P);
proof verify_proof(vector<struct proof> P);
float verify(vector<proof> proofs,int M);
int get_transcript_size(vector<proof> proofs);
float get_proof_size(vector<proof> proofs);
