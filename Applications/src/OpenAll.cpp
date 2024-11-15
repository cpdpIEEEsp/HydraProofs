#include "OpenAll.h"
#include <math.h>
#include "utils.hpp"
#include "merkle_tree.h"

extern int offset;
extern int ps;
extern double vt;

extern int application;

void VC_Commit(vector<F> poly, vector<G1> &partial_commitments, GT &C, VC_pp &pp){
    int n = (int)log2(poly.size());
    int segments,segment_size;
    partial_commitments.clear();
    if(n%2==0){
        segments = 1ULL<<(n/2 -offset );
        segment_size = 1ULL<<(n/2 + offset);
    }else{
        segments = 1ULL<<((n-1)/2 - offset);
        segment_size = 1ULL<<((n+1)/2 + offset);
        if(segments*segment_size!= poly.size()){
            printf("Error\n");
            exit(-1);
        }
    }
    vector<vector<F>> partitions(segments);
    for(int i = 0; i < segments; i++){
        partitions[i].resize(segment_size);
        for(int j = 0; j < segment_size; j++){
            partitions[i][j] = poly[i*segment_size+j];
        }
    }
    partial_commitments.resize(segments);
    for(int i = 0; i < segments; i++){
        G1::mulVec(partial_commitments[i], pp.pp1.data(), partitions[i].data(), partitions[i].size());
    }
    if(application == 3){
        mcl::bn::millerLoopVec(C,partial_commitments.data(),pp.u.data(),pp.u.size());
    }
}

void compute_proofs(vector<F> &poly, vector<vector<G1>> &pp,vector<vector<G1>> &proof_tree, int level){
	if(poly.size() == 1){

		return;
	}
	vector<F> poly1(poly.size()/2),poly2(poly.size()/2);
	vector<F> quotient(poly.size()/2);
	for(int i = 0; i < poly.size()/2; i++){
		poly1[i] = poly[2*i];
		poly2[i] = poly[2*i + 1];
		quotient[i] = poly2[i] - poly1[i];
	}
	G1 P;
	G1::mulVec(P, pp[level].data(),quotient.data(), quotient.size());	
	
	proof_tree[level].push_back(P);

	compute_proofs(poly1,pp,proof_tree,level+1);
	compute_proofs(poly2,pp,proof_tree,level+1);
}

void hyperproofs_openall(vector<F> poly,vector<vector<G1>> &pp){
	
	vector<vector<G1>> proof_tree((int)log2(poly.size()));
    compute_proofs(poly,pp,proof_tree,0);	
}

vector<F> OpenAll(vector<F> poly, vector<G1> &partial_commitments, VC_pp &pp, MIPP_Comm &pp_pc){
    int n = (int)log2(poly.size());
    int segments,segment_size;
    if(n%2==0){
        segments = 1ULL<<(n/2 -offset );
        segment_size = 1ULL<<(n/2 + offset);
    }else{
        segments = 1ULL<<((n-1)/2 - offset);
        segment_size = 1ULL<<((n+1)/2 + offset);
        if(segments*segment_size!= poly.size()){
            printf("Error\n");
            exit(-1);
        }
    }
    vector<F> r;
    vector<F> r1((int)log2(segment_size)),r2((int)log2(segments));
    // merkle commit the partital commitments
    printf("Phase 1\n");
    // Phase 1:
    // Get randomness r1;
    for(int i = 0; i < r1.size(); i++){
        r1[i].setByCSPRNG();
        r.push_back(r1[i]);
    }
    vector<F> poly_compressed(segments);
    vector<F> buff(segment_size);
    for(int i = 0; i < segments; i++){
        for(int j = 0; j < segment_size; j++){
            buff[j] = poly[i*segment_size+j];
        }
        poly_compressed[i] = evaluate_vector(buff,r1);
    }
    
    // Commit+ openall
    G1 C_compressed;
    G1::mulVec(C_compressed, pp.pp1_compressed.data(), poly_compressed.data(), poly_compressed.size());
    hyperproofs_openall(poly_compressed,pp.hyper_proofs_base_compressed);
    ps += (int)log2((poly_compressed.size()+1))*48;
    
    // Sample a second point
    for(int i = 0; i < r2.size(); i++){
        r2[i].setByCSPRNG();
        r.push_back(r2[i]);
    }
    
    vector<G1> proof_compressed;
    open(poly_compressed,r2,pp.base_compressed,proof_compressed);
   
    ps += (proof_compressed.size()+1)*48;
    verify_proof(r2,pp.pp2_compressed,pp.H,proof_compressed);
    verify_proof(r2,pp.pp2_compressed,pp.H,proof_compressed);
    if(application == 3){
        
        pp_pc.Commitments = partial_commitments;
        MIPP_open(poly,r,pp_pc);
    }
    printf("Phase 2\n");
    
    vector<vector<vector<__hhash_digest>>> MT1(r2.size());
    vector<vector<vector<__hhash_digest>>> MT2(r2.size());
    vector<vector<vector<__hhash_digest>>> MT3(r2.size());
    // Phase 2:
    for(int k = 0; k < r2.size(); k++){
        // Merkle commit the following:
        // 1) The current polynomial
        // 2) the partial evaluations
        // 3) the partial commitmnets
        // From 1+2+3 compute the new randomness
        merkle_tree::merkle_tree_prover::MT_commit(poly,segments*segment_size,MT1[k]);
        merkle_tree::merkle_tree_prover::MT_commit(poly_compressed,segments,MT2[k]);
        // Here I must add partial commitments, but i am too bored
        merkle_tree::merkle_tree_prover::MT_commit(poly_compressed,segments,MT3[k]);
        ps += ((int)log2(segments*segment_size))*32;// + 2*(int)log2(segments))*32;
        F a,b;
        a.setByCSPRNG();b.setByCSPRNG();
        for(int i = 0; i < segments/2; i++){
            for(int j = 0; j < segment_size; j++){
                poly[i*segment_size +j] = poly[(2*i)*segment_size + j]*a + poly[(2*i+1)*segment_size + j]*b; 
            }
            poly_compressed[i] = poly_compressed[2*i]*a+poly_compressed[2*i+1]*b; 
            partial_commitments[i] = partial_commitments[2*i]*a + partial_commitments[2*i+1]*b;
        }
        segments = segments/2;
    }
        
    vector<F> final_poly(segment_size);
    for(int i = 0; i < segment_size; i++){
        final_poly[i] = poly[i];
    }

    vector<G1> proof_phase2_1;
    open(final_poly,r1,pp.base,proof_phase2_1);
    verify_proof(r1,pp.pp2,pp.H,proof_phase2_1);
    verify_proof(r1,pp.pp2,pp.H,proof_phase2_1);
    hyperproofs_openall(final_poly,pp.hyper_proofs_base);
    ps += 2*proof_phase2_1.size()*48;
    
    return r;
    
}