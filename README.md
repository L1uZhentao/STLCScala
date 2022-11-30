# Simple Typed Lambda Calculus
This is course project at EPFL "F0undation of Pr0gramming Languange"

This project implements a Interpreter for Simple Typed Lambda Caculus with some extensions. 

Some examples

Example 1:

input:
```
(\x:Nat->Bool. (\y:Nat.(x y))) (\x:Nat.(iszero x)) 0
```
output:
```
typed: Bool
(\x:Nat->Bool.(\y:Nat.x y)) (\x:Nat.iszero x) 0
(\y:Nat.(\x:Nat.iszero x) y) 0
(\x:Nat.iszero x) 0
iszero 0
true
```

Example 2:

Input:
```
(\x:Nat.x) true
```
output:
```
parameter type mismatch: expected Nat, found Bool
(\x:Nat.x) true
```