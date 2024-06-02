## Description

This implements a genetic programming approach to solve the PF Max problem devised by Massey et al (https://doi.org/10.1007/978-3-540-24855-2_66) through the creation of Push style programs. Push programs consist of quantum gates and control structure elements so that they create resultant quantum programs which can be evaluted as solutions. 

## Usage

-- STILL BEING UPDATED --
To begin a GP run:

From the command line you can run:
  clj -X push411.core/main

Additionally, if you want to pass command line arguments as a map to args, you can run something like this to alter the parameters of the GP run:
  clj -X push411.core/main :selection :lexicase

From a REPL you can also just make a function call to the main function of core.clj


