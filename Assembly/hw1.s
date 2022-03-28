.data
    n: .word 7
    
.text
.globl __start

FUNCTION:

    addi sp, sp, -8      # push stack
    sw x1,4(sp)          # keep x1
    sw x10,0(sp)         # keep x10
    addi x5, x10, -1     # x5 = n - 1
    bne x5, x0, L1       # if n = 1 just go base case, else go Loop1
    addi x10, x0, 7      # base case = 7
    addi sp, sp, 8       # restore stack point
   jalr x0,0(x1) 
  L1:
    srli x10, x10, 1     # set n = floor(n/2)
    jal x1, FUNCTION           # call T(floor(n/2))
    addi x6, x10, 0      # move result T(floor(n/2)) to x6
    lw x10,0(sp)         # restore caller's n
    lw x1,4(sp)          # restore caller's return address
    addi sp, sp, 8       # pop stack
    
    slli x6, x6, 3       # get 8T(floor(n/2))
    slli x10, x10, 2     # get 4n
    add x10, x10, x6     # T(n) = 8T(n/2) + 4n
    
    jalr x0,0(x1)

# Do NOT modify this part!!!
__start:
    la   t0, n
    lw   x10, 0(t0)
    jal  x1,FUNCTION
    la   t0, n
    sw   x10, 4(t0)
    addi a0,x0,10
    ecall