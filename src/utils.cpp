//
// Created by 69029 on 6/23/2021.
//

#include "utils.hpp"
#include "config_pc.hpp"
#include "GKR.h"

#include <chrono>
using namespace std::chrono;

extern double proving_time;
extern unsigned long int mul_counter;
extern int threads;

float proof_size(vector<struct proof> P){
    int counter = 0;
    for(int i = 0; i < P.size(); i++){
        if(P[i].type== 1){
            for(int j = 1; j < P[i].randomness.size(); j++){
                counter += P[i].randomness[j].size();
            }
        }else if(P[i].type == 2){
            counter += P[i].randomness[0].size();
            counter += P[i].randomness[1].size();
        }else if(P[i].type == 3){
            counter += P[i].randomness[0].size();
        }
        counter += P[i].q_poly.size()*3;
        counter += P[i].c_poly.size()*4;
        counter += P[i].vr.size();
        counter += P[i].gr.size();
        counter += P[i].liu_sum.size();
        for(int j = 0; j < P[i].sig.size(); j++){
            counter += P[i].sig[j].size();
        }
        for(int j = 0; j  < P[i].final_claims_v.size(); j++){
            counter += P[i].final_claims_v[j].size();
        }
    }
    return (float)(counter*32)/1024.0;
}



void initHalfTable(vector<F> &beta_f, vector<F> &beta_s, const vector<F>::const_iterator &r, const F &init, u64 first_half, u64 second_half) {
    beta_f.at(0) = init;
    beta_s.at(0) = F_ONE;

    for (u32 i = 0; i < first_half; ++i) {
        for (u32 j = 0; j < (1ULL << i); ++j) {
            auto tmp = beta_f.at(j) * r[i];
            beta_f.at(j | (1ULL << i)) = tmp;
            beta_f.at(j) = beta_f[j] - tmp;
        }
    }

    for (u32 i = 0; i < second_half; ++i) {
        for (u32 j = 0; j < (1ULL << i); ++j) {
            auto tmp = beta_s[j] * r[(i + first_half)];
            beta_s[j | (1ULL << i)] = tmp;
            beta_s[j] = beta_s[j] - tmp;
        }
    }
}

void initBetaTable(vector<F> &beta_g, u8 gLength, const vector<F>::const_iterator &r, const F &init) {
    if (gLength == -1) return;

    static vector<F> beta_f, beta_s;
    int first_half = gLength >> 1, second_half = gLength - first_half;
    u32 mask_fhalf = (1ULL << first_half) - 1;

    assert(beta_g.size() >= 1ULL << gLength);
    myResize(beta_f, 1ULL << first_half);
    myResize(beta_s, 1ULL << second_half);
    if (init != F_ZERO) {
        initHalfTable(beta_f, beta_s, r, init, first_half, second_half);
        for (u32 i = 0; i < (1ULL << gLength); ++i)
            beta_g.at(i) = beta_f.at(i & mask_fhalf) * beta_s.at(i >> first_half);
    } else for (u32 i = 0; i < (1ULL << gLength); ++i)
            beta_g.at(i) = F_ZERO;

    
}

void initBetaTable(vector<F> &beta_g, int gLength, const vector<F>::const_iterator &r_0,
                   const vector<F>::const_iterator &r_1, const F &alpha, const F &beta) {
    static vector<F> beta_f, beta_s;
    int first_half = gLength >> 1, second_half = gLength - first_half;
    u32 mask_fhalf = (1ULL << first_half) - 1;
    assert(beta_g.size() >= 1ULL << gLength);
    myResize(beta_f, 1ULL << first_half);
    myResize(beta_s, 1ULL << second_half);
    if (beta != F_ZERO) {
        initHalfTable(beta_f, beta_s, r_1, beta, first_half, second_half);
        for (u32 i = 0; i < (1ULL << gLength); ++i)
            beta_g[i] = beta_f[i & mask_fhalf] * beta_s[i >> first_half];
    } else for (u32 i = 0; i < (1ULL << gLength); ++i)
            beta_g[i] = F_ZERO;

    if (alpha == F_ZERO) return;
    initHalfTable(beta_f, beta_s, r_0, alpha, first_half, second_half);
    assert(beta_g.size() >= 1ULL << gLength);
    for (u32 i = 0; i < (1ULL << gLength); ++i)
        beta_g[i] = beta_g[i] + beta_f[i & mask_fhalf] * beta_s[i >> first_half];
}

F getRootOfUnit(int n) {
    F res = -F_ONE;
    if (!n) return F_ONE;
    while (--n) {
        bool b = F::squareRoot(res, res);
        assert(b);
    }
    return res;
}

vector<F> convert2vector(vector<vector<F>> &M){
    vector<F> V;
    for(int i = 0; i < M.size(); i++){
        for(int j = 0; j < M[i].size(); j++){
            V.push_back(M[i][j]);
        }
    }
    return V;
}

vector<F> tensor2vector(vector<vector<vector<vector<F>>>> M){
    vector<F> V;

    for(int i = 0; i < M.size(); i++){
        for(int j = 0; j < M[i].size(); j++){
            for(int k = 0; k < M[i][j].size(); k++){
                for(int l = 0; l < M[i][j][k].size(); l++){
                    V.push_back(M[i][j][k][l]);
                }
            }
        }
    }
    return V;
}
void _precompute_beta(F *B, F *temp_B,F rand, vector<F> &beta, int idx, int L){
    int size = L/threads;
    int pos = idx*size;
    if(beta.size()/2 == L){
        for(int j = pos; j < pos+size; j++){
            int num = j<<1;
            F temp = rand*temp_B[j];
            beta[num] = temp_B[j] - temp;
            beta[num+1] = temp;
            
        }
    }else{
        for(int j = pos; j < pos+size; j++){
            int num = j<<1;
            F temp = rand*temp_B[j];
            B[num] = temp_B[j] - temp;
            B[num+1] = temp;
            
        }

    }
}


void compute_binary(vector<F> r, vector<F> &B){
    B.resize(1<<r.size());
    int num;
    for(int i = 0; i < 1<<r.size(); i++){
        num = i;
        B[i] = F(1);
        for(int j = 0; j < r.size(); j++){
            if(num & 1 == 1){
                B[i] = B[i]*r[j];
            }
            //else{
            //    B[i] = B[i]*(F(1)-r[j]);
            //}
            num = num >> 1;
        }

    }
}


void precompute_beta(vector<F> r,vector<F> &B){
    
    B.resize(1<<r.size());
    F *_B = (F *)malloc((1)*sizeof(F));
    B[0] = F(1);
    _B[0] = F(1);
    
    
    for(int i = 0; i < r.size(); i++){
        
        F *temp_B = (F *)malloc((1<<(i+1))*sizeof(F));
        
        //vector<F> temp_B(1<<i);
        //for(int j = 0; j < (1<<i); j++){
        //    temp_B[j] = (_B[j]);
        //}
        if(threads == 1 || 1<<10 >= 1<<i){
            
            if(B.size()/2 == 1<<i){
                for(int j = 0; j < (1<<i); j++){
                    int num = j<<1;
                    //printf("%d\n",num);
                    F temp = r[r.size() - 1 -i]*_B[j];
                    B[num] = _B[j] - temp;
                    B[num+1] = temp;
                
                }
            }else{
                
                for(int j = 0; j < (1<<i); j++){
                    int num = j<<1;
                    //printf("%d\n",num);
                    F temp = r[r.size() - 1 -i]*_B[j];
                    temp_B[num] = _B[j] - temp;
                    temp_B[num+1] = temp;
                    
                    /*
                    B[num] = (1-r[r.size() - 1 -i])*temp_B[j];
                    B[num+1] = r[r.size() - 1 -i]*temp_B[j];
                    */
                }
            }
        }else{
            thread workers[threads];
            for(int j = 0; j < threads; j++){
                workers[j] = thread(&_precompute_beta,temp_B,_B,r[r.size() - 1 -i],ref(B),j,1<<i);
            }
            for(int j = 0; j < threads; j++){
                workers[j].join();
            }
        }
        _B = temp_B;
    }
    //return B;
}
void write_data(vector<F> data,char *filename){
    FILE *f;
    char buff[257];
    f = fopen(filename,"w+");
    
    for(int i= 0; i < data.size(); i++){
        data[i].getStr(buff,257,10);
        fprintf(f, "%s\n",buff);
    }
    fclose(f);
    
}

vector<vector<vector<vector<F>>>> vector2tensor(vector<F> v,vector<vector<vector<vector<F>>>> M,int w_pad){
    int N = M[0].size();
    int w = M[0][0].size();
    vector<vector<vector<vector<F>>>> M_new(M.size());
    for(int i = 0; i < M.size(); i++){
        M_new[i].resize(M[i].size());
        for(int j = 0; j < M[i].size(); j++){
            M_new[i][j].resize(w_pad);
            for(int k = 0; k < w_pad; k++){
                M_new[i][j][k].resize(w_pad);
                for(int l = 0; l < w_pad; l++){
                    M_new[i][j][k][l] = v[i*N*w*w + j*w*w + k*w + l];
                    //V.push_back(M[i][j][k][l]);
                }
            }
        }
    }
    return M_new;
}

vector<vector<F>> convert2matrix(vector<F> arr, int d1, int d2){
    vector<vector<F>> U(d1);
    for(int i = 0; i < d1; i++){
        U[i].resize(d2);
        for(int j = 0; j < d2; j++){
            U[i][j] = arr[i*d2+j];
        }
    }
    return U;
}


vector<vector<F>> &transpose(vector<vector<F>> &M){
    vector<vector<F>> M_t(M[0].size());
    for(int i = 0; i < M[0].size(); i++){
        M_t[i].resize(M.size());
        for(int j = 0; j < M.size(); j++){
            M_t[i][j] = M[j][i];
        }
    }
    return M_t;
}

vector<vector<F>> _transpose(vector<vector<F>> &M){
    vector<vector<F>> M_t(M[0].size());
    for(int i = 0; i < M[0].size(); i++){
        M_t[i].resize(M.size());
        for(int j = 0; j < M.size(); j++){
            M_t[i][j] = M[j][i];
        }
    }
    return M_t;
}


vector<vector<F>> rotate(vector<vector<F>> M){
    vector<vector<F>> M_r(M.size());
    for(int i = 0; i < M.size(); i++){
        M_r[i].resize(M[i].size());
        for(int j = 0; j < M[i].size(); j++){
            M_r[i][j] = M[M.size()-1-i][M[i].size()-1-j];
        }
    }
    return M_r;
}




vector<F> prepare_bit_vector(vector<F> num, int domain){
    vector<F> bits;
    for(int i = 0; i < num.size(); i++){
        vector<F> temp_bits;
        char buff[257];
        for(int j = 0; j < domain; j++){
            temp_bits.push_back(F(0));
        }
        int n = num[i].getStr(buff,257,2);
        if(domain > n-1){
            for(int j = n-1; j >= 0; j--){
                if(buff[j] == '1'){
                    temp_bits[n-1 - j] = F(1);
                }
            }
        }else{
            printf("Select larger domain %d\n",n);
            exit(-1);
        }
        for(int j = 0; j < domain; j++){
            bits.push_back(temp_bits[j]);
        }
    }
    return bits;
}

void fft(vector<F> &arr, int logn, bool flag) {
//    cerr << "fft: " << endl;
//    for (auto x: arr) cerr << x << ' ';
//    cerr << endl;
    static std::vector<u32> rev;
    static std::vector<F> w;

    u32 len = 1ULL << logn;
    assert(arr.size() == len);

    rev.resize(len);
    w.resize(len);

    rev[0] = 0;
    for (u32 i = 1; i < len; ++i)
        rev[i] = rev[i >> 1] >> 1 | (i & 1) << (logn - 1);

    w[0] = F_ONE;
    w[1] = getRootOfUnit(logn);
    char buff[256];
    w[1].getStr(buff,256,10);
   
   
    if (flag) F::inv(w[1], w[1]);
    for (u32 i = 2; i < len; ++i) w[i] = w[i - 1] * w[1];
    mul_counter += len-2;
    for (u32 i = 0; i < len; ++i)
        if (rev[i] < i) std::swap(arr[i], arr[rev[i]]);

    for (u32 i = 2; i <= len; i <<= 1)
        for (u32 j = 0; j < len; j += i)
            for (u32 k = 0; k < (i >> 1); ++k) {
                auto u = arr[j + k];
                auto v = arr[j + k + (i >> 1)] * w[len / i * k];
                arr[j + k] = u + v;
                arr[j + k + (i >> 1)] = u - v;
                mul_counter++;
            }

    if (flag) {
        F ilen;
        F::inv(ilen, len);
        for (u32 i = 0; i < len; ++i){
            arr[i] = arr[i] * ilen;
            mul_counter++;
        }
    }
}


void phiPowInit(vector<F> &phi_mul, int n, bool isIFFT) {
    u32 N = 1ULL << n;
    F phi = getRootOfUnit(n);
    if (isIFFT) F::inv(phi, phi);
    phi_mul[0] = F_ONE;
    for (u32 i = 1; i < N; ++i) phi_mul[i] = phi_mul[i - 1] * phi;
}

void phiGInit(vector<F> &phi_g, const vector<F>::const_iterator &rx, const F &scale, int n, bool isIFFT) {
    vector<F> phi_mul(1 << n);
    phiPowInit(phi_mul, n, isIFFT);

    if (isIFFT) {
//        cerr << "==" << endl;
//        cerr << "gLength: " << n << endl;
//        for (int i = 0; i < n - 1; ++i) {
//            cerr << rx[i];
//            cerr << endl;
//        }
        phi_g[0] = phi_g[1] = scale;
        for (int i = 2; i <= n; ++i)
            for (u32 b = 0; b < (1ULL << (i - 1)); ++b) {
                u32 l = b, r = b ^ (1ULL << (i - 1));
                int m = n - i;
                F tmp1 = F_ONE - rx[m], tmp2 = rx[m] * phi_mul[b << m];
                phi_g[r] = phi_g[l] * (tmp1 - tmp2);
                phi_g[l] = phi_g[l] * (tmp1 + tmp2);
            }
    } else {
//        cerr << "==" << endl;
//        cerr << "gLength: " << n << endl;
//        for (int i = 0; i < n; ++i) {
//            cerr << rx[i];
//            cerr << endl;
//        }
        phi_g[0] = scale;
        /*
        
        for(int i = 0; i < n; i++){
            for(int j = 1ULL << (i+1)-1; j >= 0; j--){
                phi_g[j] = phi_g[j%(1ULL << i)]*(F(1)-rx[i] + rx[i]*phi_mul[j]);
            }
        }
        */

        for (int i = 1; i < n; ++i){
            for (u32 b = 0; b < (1ULL << (i - 1)); ++b) {
                u32 l = b, r = b ^ (1ULL << (i - 1));
                int m = n - i;
                
                F tmp1 = F_ONE - rx[m], tmp2 = rx[m] * phi_mul[b << m];
                //printf("%d,%d\n",r,l );
                phi_g[r] = phi_g[l] * (tmp1 - tmp2);
                phi_g[l] = phi_g[l] * (tmp1 + tmp2);
            }

        }
        for (u32 b = 0; b < (1ULL << (n - 1)); ++b) {
            u32 l = b;

            F tmp1 = F_ONE - rx[0], tmp2 = rx[0] * phi_mul[b];
            phi_g[l] = phi_g[l] * (tmp1 + tmp2);
            
        }
        
    }
}

void _prepare_matrix1(vector<vector<F>> &M,F rand, int idx, int n, int L){
    int size = n/threads;
    int pos = idx*size;
   
    for(int i = pos; i < pos + size; i++){
        for(int j = 0; j < L; j++){
            M[i][j] = M[i][2*j] + rand*(M[i][2*j+1]-M[i][2*j]);
        }
    }
}
void _prepare_matrix2(F** M,F **temp_M, F rand, int idx, int n, int L){
    int size = L/threads;
    int pos = idx*size;
    

    for(int i = 0; i < n; i++){
        for(int j = pos; j < pos + size ; j++){
            temp_M[i][j] = M[i][2*j] + rand*(M[i][2*j+1]-M[i][2*j]);
        }
    }
}

void cp(vector<vector<F>> &M1,vector<vector<F>> &M2){
    M1 = ref(M2);
}

vector<F> prepare_matrix(vector<vector<F>> &M, vector<F> r){
    vector<F> V;
    int n = M.size();
    int offset = M[0].size()/2;
    //printf(">> %d,%d,%d\n",n, M[0].size(),r.size() );
   
     if(threads == 1){
        for(int k = 0; k < r.size(); k++){
            for(int i = 0; i < n; i++){
                for(int j = 0; j < offset; j++){
                    M[i][j] = M[i][2*j] + r[k]*(M[i][2*j+1]-M[i][2*j]);
                }
            }
            offset = offset/2;
        }
    }
    else if(n >= threads){

        for(int k = 0; k < r.size(); k++){
            if(n*offset > 1<<16){
        
                thread workers[threads];
                for(int i = 0; i < threads; i++){
                    workers[i] = thread(&_prepare_matrix1,ref(M),r[k],i,n,offset);
                }
                for(int i = 0; i < threads; i++){
                    workers[i].join();
                }
            }else{
                for(int i = 0; i < n; i++){
                    for(int j = 0; j < offset; j++){
                        M[i][j] = M[i][2*j] + r[k]*(M[i][2*j+1]-M[i][2*j]);
                    }
                }
            }
            offset = offset/2;
        }
    }else{
        F** temp = (F **)malloc(n*sizeof(F *));
        for(int i = 0; i < n; i++){
            temp[i] = M[i].data();
        }
        
        for(int k = 0; k < r.size(); k++){
            if(n*offset > 1<<16){
                F **temp_M;
                temp_M = (F **)malloc(n*sizeof(F*));
                for(int i = 0; i < n; i++){
                    temp_M[i] = (F *)malloc(offset*sizeof(F));
                }
                
                thread workers[threads];
                auto ts = high_resolution_clock::now();
                for(int i = 0; i < threads; i++){
                    workers[i] = thread(&_prepare_matrix2,ref(temp),ref(temp_M),r[k],i,n,offset);
                }
                for(int i = 0; i < threads; i++){
                    workers[i].join();
                }
                offset = offset/2;
                
                auto te = high_resolution_clock::now();
                auto tduration = duration_cast<microseconds>(te - ts);
                
                ts = high_resolution_clock::now();
                
                for(int i = 0; i < n; i++){
                    temp[i] = temp_M[i];
                }

                te = high_resolution_clock::now();
                tduration = duration_cast<microseconds>(te - ts);
                
            }else{
                for(int i = 0; i < n; i++){
                    for(int j = 0; j < offset; j++){
                        temp[i][j] = temp[i][2*j] + r[k]*(temp[i][2*j+1]-temp[i][2*j]);
                    }
                }   
            }
        }
        for(int i = 0; i < n; i++){
            V.push_back(temp[i][0]);
        }
        return V;
    }
    for(int i = 0; i < n; i++){
        V.push_back(M[i][0]);
    }
    return V;
}

F evaluate_matrix(vector<vector<F>> M, vector<F> r1, vector<F> r2){
    vector<F> v = prepare_matrix(transpose(M),r1);
    for(int i = 0; i < r2.size(); i++){
        int L = 1 << (r2.size() - 1 - i);

        for(int j = 0; j < L; j++){
            v[j] = (1-r2[i])*v[2*j] + r2[i]*v[2*j+1];
        }
    }
    return v[0];
}

F evaluate_vector(vector<F> v,vector<F> r){
    if(r.size() > (int)log2(v.size())){
        vector<F> temp_r;
        for(int i = 0; i < (int)log2(v.size()); i++){
            temp_r.push_back(r[r.size()-(int)log2(v.size())+ i]);
        }
        r = temp_r;
    }
    for(int i = 0; i < r.size(); i++){
        int L = 1 << (r.size() - 1 - i);
        for(int j = 0; j < L; j++){
            v[j] = (1-r[i])*v[2*j] + r[i]*v[2*j+1];
        }
    }
    return v[0];    
}




vector<vector<F>> generate_tables(){
    int N = 4;
    int no_tables = 5;
    vector<vector<F>> tables(no_tables);
    vector<int> max_num;
    int exponent = 0,last_exponent = 1;
    float num = 0;
    
    for(int i = 0; i < tables.size(); i++){
        for(int j = 0; j < 1<<N; j++){
            exponent = exponent + last_exponent; 
            F num;
            num.setByCSPRNG();
            tables[i].push_back(num);
            //tables[i].push_back(quantize(exp(-dequantize(exponent,1))));
        }
        last_exponent = exponent;
        exponent = 0;
    }
    
    //printf("%f,%f\n",dequantize(prod,level),exp(-0.1) );
    return tables;
}


vector<F> get_predicates(int size){
    vector<F> poly;
    for(int i = 0; i < 1<<size; i++){
        poly.push_back(F(rand()%2));
    }
    return poly;
}

vector<F> get_poly(int size){
    vector<F> poly;

    for(int i = 0; i < 1<<size; i++){
        F num;
        num.setByCSPRNG();
        poly.push_back(num);
    }
    return poly;
}

vector<F> lookup_prod(vector<vector<F>> tables, F num){
    char buff[256];
    num = F(0)-num;
    int n = num.getStr(buff,256,2);
    int counter = 0;
    int level = 0;
    F prod = F(1);
    vector<vector<F>> monomials(tables.size());
    for(int i = 0; i < tables.size(); i++){
        monomials[i].resize(4);
        for(int j = 0; j < 4; j++){
            monomials[i][j] = F(0);
        }
    }
    for(int i = 0; i < tables.size(); i++){
        int idx = 0;

        for(int j = 0; j < (int)log2(tables[i].size()); j++){
            if(buff[n - counter - 1] == '1'){
                idx += 1<<j;
                monomials[i][j] = F(1);
            }
            

            counter+=1;
            if(counter == n){
                break;
            }

        }
        if(counter == n){
            prod *= tables[i][idx];
            level = i+1;
            break;
        }
        level = i+1;
        prod *= tables[i][idx];
    }
    if(level < tables.size()){
    
        for(int i = level; i <tables.size(); i++){
            prod *= tables[i][0];
        }
    }
    vector<F> r;
    F prod_2 = F(1);
    for(int i = 0; i < monomials.size(); i++){
        r.push_back( evaluate_vector(tables[i],monomials[i]));
    }


    return r;
}

F lookup(vector<vector<F>> tables, F num){
    char buff[256];
    num = F(0)-num;
    int n = num.getStr(buff,256,2);
    int counter = 0;
    int level = 0;
    F prod = F(1);
    vector<vector<F>> monomials(tables.size());
    for(int i = 0; i < tables.size(); i++){
        monomials[i].resize(4);
        for(int j = 0; j < 4; j++){
            monomials[i][j] = F(0);
        }
    }
    for(int i = 0; i < tables.size(); i++){
        int idx = 0;

        for(int j = 0; j < (int)log2(tables[i].size()); j++){
            if(buff[n - counter - 1] == '1'){
                idx += 1<<j;
                monomials[i][j] = F(1);
            }
            

            counter+=1;
            if(counter == n){
                break;
            }

        }
        if(counter == n){
            prod *= tables[i][idx];
            level = i+1;
            break;
        }
        level = i+1;
        prod *= tables[i][idx];
    }
    if(level < tables.size()){
    
        for(int i = level; i <tables.size(); i++){
            prod *= tables[i][0];
        }
    }

    F prod_2 = F(1);
    for(int i = 0; i < monomials.size(); i++){
        prod_2 *= evaluate_vector(tables[i],monomials[i]);
    }

    prod_2.getStr(buff,256,10);
    //printf("%s\n",buff );

    return prod;
}
