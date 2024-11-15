cmake_minimum_required(VERSION 3.10)
project(ProofOfLearning)

set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_FLAGS "-w -march=native -O3 -faligned-new -mavx -lgmp -pthread")
set(CMAKE_C_FLAGS "-w -march=native -O3 -faligned-new -mavx -lgmp -pthread")

link_directories(3rd/mcl)

link_directories(lib)

include_directories(src)
include_directories(3rd)
include_directories(3rd/mcl/include)
include_directories(lib)



add_subdirectory(src)
add_subdirectory(3rd/mcl)
