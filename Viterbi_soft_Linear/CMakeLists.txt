cmake_minimum_required(VERSION 3.25)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/bin")
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/lib")
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/lib")

project(Berlekamp-Massey_binary_BCH LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)

add_executable(main src/main.cpp)