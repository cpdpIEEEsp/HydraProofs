
#include "config_pc.hpp"
#include "merkle_tree.h"
#include <vector>
#include <math.h>

using namespace std;

int merkle_tree::size_after_padding;


void merkle_tree::get_int32(vector<unsigned int> &arr, __hhash_digest hash){
    unsigned int* res_array = reinterpret_cast<unsigned int*>(&hash.h0);
    for (int i = 0; i < 4; ++i) {
        arr[i] = res_array[i];
    }
    res_array = reinterpret_cast<unsigned int*>(&hash.h1);
    for(int i = 4; i < 8; i++){
        arr[i] = res_array[i-4];        
    }
}




__hhash_digest merkle_tree::hash_double_field_element_merkle_damgard(F x, F y, __hhash_digest prev_hash)
{
   __hhash_digest data[2], ret;
    //data[0] = prev_hash;
    F element[2];
    element[0] = x;
    element[1] = y;
    memcpy(&data[0], &element[0],  sizeof(F));
    memcpy(&data[1], &element[1],  sizeof(F));
    my_hhash(data, &ret);
    return ret;
}
    

void merkle_tree::merkle_tree_prover::create_tree_sha(int ele_num, vector<vector<__hhash_digest>> &dst_ptr, int level, const int element_size = 256 / 8, bool alloc_required = false){
    int current_lvl_size = ele_num;
    //#pragma omp parallel for
   
    int curr_level = 1;
    current_lvl_size /= 2;
    while(curr_level != level)
    {
        //printf("%d,%d,%d\n",current_lvl_size,dst_ptr[curr_level].size(),curr_level);
        #pragma omp parallel for
        for(int i = 0; i < current_lvl_size; ++i)
        {
            //printf("%d,%d\n",start_ptr + current_lvl_size + i * 2,start_ptr + current_lvl_size + i * 2+1);
            __hhash_digest data[2];
            data[0] = dst_ptr[curr_level-1][i * 2];
            data[1] = dst_ptr[curr_level-1][i * 2 + 1];
            my_hhash(data, &dst_ptr[curr_level][i]);
        }
        curr_level++;
        current_lvl_size /= 2;
    }
}

void merkle_tree::merkle_tree_prover::MT_commit(vector<F> &leafs,int size,vector<vector<__hhash_digest>> &hashes){
    vector<__hhash_digest> leaf_hashes(size/2);
    __hhash_digest data[2], ret;
    //data[0] = prev_hash;
    F element[2];
    char buff[32];
    //#pragma omp parallel for
    for(int i = 0; i < size/2; i++){
        int n = leafs[2*i].getStr(buff,32);
        leafs[2*i].serialize(buff,32);
       
        memcpy(&data[0], buff, 32);
       
        leafs[2*i+1].serialize(buff,32);
        memcpy(&data[1], buff, 32);
       
        my_hhash(data, &leaf_hashes[i]);
    }
    
    
    if(hashes.size() == 0){
        hashes.resize((int)log2(leaf_hashes.size())+1);
    }
    hashes[0] = leaf_hashes;
    merkle_tree::merkle_tree_prover::create_tree( leaf_hashes.size() , leaf_hashes, hashes, sizeof(__hhash_digest), true);
}

__hhash_digest merkle_tree::merkle_tree_prover::create_tree(int ele_num, vector<__hhash_digest> &dst_ptr, vector<vector<__hhash_digest>> &hashes, const int element_size = 256 / 8, bool alloc_required = false)
{
    //assert(element_size == sizeof(prime_field::field_element) * 2);
    
    int current_lvl_size = ele_num;
    
    int level = 1;
    current_lvl_size /= 2;
    __hhash_digest data[2];
    int lvl = 1;
    
    while(current_lvl_size >= 1)
    {
        if(lvl >= 0){
            hashes[lvl].resize(current_lvl_size);
        }
        #pragma omp parallel for
        for(int i = 0; i < current_lvl_size; ++i)
        {
            //printf("%d,%d\n",start_ptr + current_lvl_size + i * 2,start_ptr + current_lvl_size + i * 2+1);
            data[0] = dst_ptr[ i * 2];
            data[1] = dst_ptr[ i * 2 + 1];
            my_hhash(data, &dst_ptr[i]);
            if(lvl >= 0){
                hashes[lvl][i] = dst_ptr[i];
            }
        }
        lvl++;
        current_lvl_size /= 2;
    }
    //dst = dst_ptr.data();
    return dst_ptr[0];
}


vector<__hhash_digest> merkle_tree::merkle_tree_prover::open_tree(vector<vector<__hhash_digest>> &MT_hashes, vector<size_t> c,  int collumns){
    int pos = (c[1]/4)*collumns + c[0];
    vector<__hhash_digest> path;
    for(int i = 0; i < MT_hashes.size(); i++){
        path.push_back(MT_hashes[i][2*(pos/2) + (1-(pos%2))]);
        pos = pos/2;
    }
    return path;
}

bool merkle_tree::merkle_tree_verifier::verify_claim(__hhash_digest root_hhash, const __hhash_digest* tree, __hhash_digest leaf_hash, int pos_element_arr, int N)
{
    //check N is power of 2
    assert((N & (-N)) == N);

    int pos_element = pos_element_arr + N;
    __hhash_digest data[2];
    while(pos_element != 1)
    {
        data[pos_element & 1] = leaf_hash;
        data[(pos_element & 1) ^ 1] = tree[pos_element ^ 1];
        my_hhash(data, &leaf_hash);
        pos_element /= 2;
    }
    return equals(root_hhash, leaf_hash);
}