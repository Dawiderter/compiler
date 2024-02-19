# JFTT 2023 Compiler 

This program was made for the Formal Languages and Compilators class at Wrocław University of Science and Technology.
It compiles a simple imperative language to a simple register-based virtual machine. Assignment's author is dr Maciej Gębala from Department of Fundamentals of Computer Science.

## Running 
To build you only need Rust Toolchain.
Then you can run the compiler with:
```bash
cargo run -- <input file> <output file>
```

## Features
Compiler works in many separate passes:
- Lexing
- Parsing to AST
- Checking and optimizing AST
- Turning AST to MIR
- Optimizing MIR with graph-based register allocation
- Turning MIR to VM code

### Optimizations
First and important optimization is inlining and eliminating certain procedures. At AST level if procedure is only used once, it is inlined at the call site. Then if procedure is never used, it is eliminated from the tree entirely.

When building MIR there are created many temporary registers which later get assigned to physical registers or cell in memory with register allocation algorithm based on interference graph coloring. 

## Grammar
```
program_all  -> procedures main

procedures   -> procedures PROCEDURE proc_head IS declarations IN commands END
             | procedures PROCEDURE proc_head IS IN commands END
             | 

main         -> PROGRAM IS declarations IN commands END
             | PROGRAM IS IN commands END

commands     -> commands command
             | command

command      -> identifier := expression;
             | IF condition THEN commands ELSE commands ENDIF
             | IF condition THEN commands ENDIF
             | WHILE condition DO commands ENDWHILE
             | REPEAT commands UNTIL condition;
             | proc_call;
             | READ identifier;
             | WRITE value;

proc_head    -> pidentifier ( args_decl )

proc_call    -> pidentifier ( args )

declarations -> declarations, pidentifier
             | declarations, pidentifier[num]
             | pidentifier
             | pidentifier[num]

args_decl    -> args_decl, pidentifier
             | args_decl, T pidentifier
             | pidentifier
             | T pidentifier

args         -> args, pidentifier
             | pidentifier

expression   -> value
             | value + value
             | value - value
             | value * value
             | value / value
             | value % value

condition    -> value = value
             | value != value
             | value > value
             | value < value
             | value >= value
             | value <= value

value        -> num
             | identifier

identifier   -> pidentifier
             | pidentifier[num]
             | pidentifier[pidentifier]
```

## Virtual Machine
Virtual machine consisted of 8 registers from Ra to Rh with additional register k representing number of currently executed line and infinite memory with cells containing infinitly large nonnegative integer numbers. It is able to read and execute following instructions:

| Instruction | Interpretation | Time |
| --- | --- | --- |
| READ | Read a number, save it in Ra and k ← k + 1 | 100 |
| WRITE | Show content of Ra and k ← k + 1 | 100 |
| LOAD x | Ra ← P[Rx] and k ← k + 1 | 50 |
| STORE x | P[Rx] ← Ra and k ← k + 1 | 50 |
| ADD x | Ra ← Ra + Rx and k ← k + 1 | 5 |
| SUB x | Ra ← max{Ra − Rx, 0} and k ← k + 1 | 5 |
| GET x | Ra ← Rx and k ← k + 1 | 1 |
| PUT x | Rx ← Ra and k ← k + 1 | 1 |
| RST x | Rx ← 0 and k ← k + 1 | 1 |
| INC x | Rx ← Rx + 1 and k ← k + 1 | 1 |
| DEC x | Rx ← max{Rx − 1, 0} and k ← k + 1 | 1 |
| SHL x | Rx ← 2 ∗ Rx and k ← k + 1 | 1 |
| SHR x | Rx ← ⌊Rx/2⌋ and k ← k + 1 | 1 |
| JUMP j | k ← j | 1 |
| JPOS j | If Ra > 0 then k ← j else k ← k + 1 | 1 |
| JZERO j | If Ra = 0 then k ← j else k ← k + 1 | 1 |
| STRK x | Rx ← k and k ← k + 1 | 1 |
| JUMPR x | k ← Rx | 1 |
| HALT | Stop execution | 0 |