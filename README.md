# Single-Cycle-RISC-V

## Description

This is the final project for Computer Architecture course (EE4039@NTUEE). It supports the following instructions:

◆ auipc, jal, jalr  
◆ beq, lw, sw  
◆ addi, slti, add, sub  
◆ mul  
◆ srai, slli

## Executing Program

A testbench (Final_tb.v) is provided. The behavior of the chip can be simulated by using the following commands: 
```
ncverilog Final_tb.v +define+leaf +access+r
ncverilog Final_tb.v +define+fact +access+r
ncverilog Final_tb.v +define+hw1 +access+r
```
To see the simulated wave form, use nWave:
```
nWave &
```
and read the generated fsdb file.

## Architecture

![alt text](https://github.com/[username]/[reponame]/blob/[branch]/image.jpg?raw=true)

## Authors

Contributors names and contact info

Hao-Wei, Liang(b07502022@ntu.edu.tw) 

Yen-An, Lu(b07501003@ntu.edu.tw)
  
Yu-An, Lin(b06204039@ntu.edu.tw)

