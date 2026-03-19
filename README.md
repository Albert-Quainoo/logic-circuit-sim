# Logic Circuit Simulator

A Python-based logic circuit simulator for modeling and evaluating Boolean expressions using digital gate abstractions.

## Overview

This project was developed for a Discrete Mathematics course project. It allows users to enter Boolean expressions, simulate the corresponding logic circuit, and generate outputs such as truth tables, circuit build steps, and output summaries.

The simulator parses logical expressions, converts them into an internal circuit representation, and evaluates the resulting output across all possible input combinations. It also supports compound logic behavior such as XOR, NAND, NOR, and XNOR.

In addition to the core simulation logic, the project includes optional visualisation features and a GUI-based workbench for interacting with expressions more easily.

## Features

- Parse Boolean expressions into circuit structures
- Generate truth tables for all input combinations
- Simulate logic outputs from user-defined expressions
- Support common logic operations:
  - NOT
  - AND
  - OR
  - XOR
  - NAND
  - NOR
  - XNOR
- Show step-by-step circuit construction from the parsed expression
- Plot truth tables and output distributions with Matplotlib
- Launch a GUI workbench using PyQt6 for interactive use

## Expression Syntax

The simulator maps user-level logical syntax into internal operations.

### Supported operators

| Symbol | Meaning |
|--------|---------|
| `!` | NOT |
| `*` | AND |
| `+` | OR |
| `^` | XOR |
| `%` | NAND |
| `~` | NOR |
| `#` | XNOR |

### Example expressions

```text
A * B
!(A + B)
A ^ B
(A % B) + C
(A ~ B)
(A # B)
```

## External Dependency 

This project relies on the on the `circuit` module from the open-source repository below:

* Source: `https://github.com/olooney/circuit`

## Libraries Used

* AST library for expression parsing
* Matplotlib for visualisation
* PyQt6 for the graphical interface


## How It Works

1. The user enters a Boolean expression.
2. The expression is translated into an internal Python-compatible form.
3. The program parses the expression as an abstract syntax tree.
4. The AST is walked recursively to build the logic circuit.
5. The simulator evaluates the circuit for every possible input combination.
6. The results are displayed as a truth table, step trace, or visualization.

## Running The Project

### Basic run

`python circuit_sim_adv.py`

### Optional dependencies

If you want to use plotting and GUI features, install the required libraries:

`pip install matplotlib PyQt6`

If these libraries are not installed, the simulator can still run core logic features, but plotting and GUI features may be unavailable.

## Example Outputs

The simulator can produce:
* Truth tables for Boolean expressions
* Step-by-step simulation traces
* Circuit build logs
* Output distribution plots
* Interactive GUI-based exploration

