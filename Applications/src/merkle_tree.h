#pragma once
#ifndef __merkle_tree
#define __merkle_tree
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <immintrin.h>
#include <wmmintrin.h>
#include "config_pc.hpp"
#include "my_hhash.h"

namespace merkle_tree
{
extern int size_after_padding;

void get_int32(vector<unsigned int> &arr, __hhash_digest hash);

__hhash_digest hash_single_field_element(F x);

__hhash_digest hash_double_field_element_merkle_damgard(F x, F y, __hhash_digest prev_hash);

namespace merkle_tree_prover
{
    //Merkle tree functions used by the prover
    //void create_tree(void* data_source_array, int lengh, void* &target_tree_array, const int single_element_size = 256/8)
    __hhash_digest create_tree(int ele_num, vector<__hhash_digest> &dst_ptr,vector<vector<__hhash_digest>> &hashes, const int element_size, bool alloc_required);
    void _create_tree(void* src_data, int ele_num, __hhash_digest* &dst, const int element_size, bool alloc_required);
    void MT_commit(vector<F> &leafs,int size,vector<vector<__hhash_digest>> &hashes);
    void create_tree_mimc( int ele_num, vector<vector<F>> &dst_ptr, int level, const int element_size, bool alloc_required );
    void create_tree_sha( int ele_num, vector<vector<__hhash_digest>> &dst_ptr, int level, const int element_size, bool alloc_required);
    vector<__hhash_digest> open_tree(vector<vector<__hhash_digest>> &MT_hashes, vector<size_t> c,  int collumns);

}

namespace merkle_tree_verifier
{
    //Merkle tree functions used by the verifier
    bool verify_claim(__hhash_digest root_hhash, const __hhash_digest* tree, __hhash_digest hhash_element, int pos_element, int N);
}
}

#endif