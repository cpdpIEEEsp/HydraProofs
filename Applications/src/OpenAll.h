#include "Poly_Commit.h"
#include "config_pc.hpp"


void VC_Commit(vector<F> poly, vector<G1> &partial_commitments, GT &C, VC_pp &pp);
vector<F> OpenAll(vector<F> poly, vector<G1> &partial_commitments, VC_pp &pp, MIPP_Comm &pp_pc);
void hyperproofs_openall(vector<F> poly,vector<vector<G1>> &pp);