## Description

This implements a genetic programming approach to solve the PF Max problem devised by Massey et al (https://doi.org/10.1007/978-3-540-24855-2_66) through the creation of Push style programs. Push programs consist of quantum gates and control structure elements so that they create resultant quantum programs which can be evaluted as solutions. 

When the program is ran, a population of quantum programs is created and undergo parent selection and crossover/mutation to create programs for the next generation. This is done either until a solution is found or a target number of generations is reached.

## Usage
To begin a GP run:

From the command line navigate to the directory /quantum_gp_pf_max. Then, you can run:
  clj -X gp.core/main

This will make a function call to the main GP call, starting the training of a population of programs.

Additionally, if you want to pass command line arguments as a map to args (changing the parameters of the GP run), you can run something like this to alter the parameters of the GP run:
  clj -X gp.core/main :selection :lexicase

Lastly, from a REPL (such as Calva) you can also just make a function call to the main function of core.clj after loading the contents of quantum_gp_pf_max/src/gp.

## Credits

This project includes code from the following source:

- **[Mikera](https://github.com/mikera)**: [https://github.com/mikera/core.matrix.complex?tab=EPL-1.0-1-ov-file]
  - License: [Eclipse Public License - v 1.0]

The original code has been integrated into this project with permission/compliance with the original license.
