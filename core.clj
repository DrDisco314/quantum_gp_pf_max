(ns push411.core
  (:require [push411.qgate :as qgate]
            [clojure.core.matrix :as m]
            [clojure.math.combinatorics :as combo]
            [clojure.math.numeric-tower :as math]))


(comment
  "NAME: Alexander Axton
   This is the final implementation of my GP term project. This program evolves a series
   of quantum logic circuits programs using GP to ultimately solve the PF Max problem,
   
   Problem: Given ANY permutation function f(x) that is supplied as input
   and which operates on the integer range [0..3], use a suitable encoding
   to evolve a quantum program, U, that returns the value of x that gives
   the maximum value of f(x).

   As a novel method, I have implemented a compose function that identifies some subsequence
   of quantum gates across multiple programs and composes it into a single gate to be added to
   programs during evolution.

   To do this, programs are generated in evaluated in Push and uniform operators are implemented
   such as uniform-addition, uniform-deletion, and crossover to mutate individuals Parent selection
   is performed using tournament selection.
   ")

;;;;;;;;;;
;; Examples

; An example Push state
(def q-example-push-state
  {:exec '(qgate_cnot qgate_cnot)
   :integer '(0 1 2 3)
   :qgate '()})

; Another Push state for quick testing
(def q-example-push-state-1
  {:exec '(exec_dup qgate_cnot qgate_swap qgate_toffoli)
   :integer '(0 1 2 3 0 1 2 3 0 1 2 3)
   :qgate '()})

; An example Plushy genome
(def q-example-plushy-genome
  '(0 2 exec_dup 0 1 close qgate_cnot 3 2 0 qgate_cnot))

; An example Push program
; This is the program that would result from the above Plushy genome
(def q-example-push-program
  '(0 2 exec_dup 0 1 qgate_cnot 3 2 0 qgate_cnot))

; An example individual in the population
; Made of a map containing, at mimimum, a program, the errors for
; the program, and a total error
(def example-individual
  {:genome '(0 2 exec_dup 0 1 qgate_cnot 3 2 0 qgate_cnot close)
   :program '(0 2 exec_dup 0 1 qgate_cnot 3 2 0 qgate_cnot)
   :errors []
   :total-error 2.80115000650})

;;;;;;;;;;
; Instructions must all be either functions that take one Push state and return another
; or constant literals.
; The exception is `close`, which is only used in translation from Plushy to Push

;; Default instruction set to be used
(def default-instructions
  (list
   `qgate_not
   `qgate_haddamard
   `qgate_controlled_z
   `qgate_cnot
   `qgate_swap
   `qgate_toffoli
   `exec_dup
   'close
   0
   1
   2
   3
   0
   1
   2
   3
   0
   1
   2
   3
   0
   1
   2
   3))

; number of code blocks opened by instructions (default = 0)
(def opened-blocks
  {`exec_dup 1})

;;;;;;;;;
;; Utilities

;; Empty push state to use for initializing the state of programs.
(def empty-push-state
  {:exec '()
   :integer '()
   :qgate '()})

(defn push-to-stack
  "Pushes item onto stack in state, returning the resulting state."
  [state stack item]
  (let [new-stack (conj (state stack) item)]
    (assoc state stack new-stack)))

(defn pop-stack
  "Removes top item of stack, returning the resulting state."
  [state stack]
  (let [new-stack (rest (state stack))]
    (assoc state stack new-stack)))

(defn peek-stack
  "Returns top item on a stack. If stack is empty, returns :no-stack-item"
  [state stack]
  (let [item (first (state stack))]
    (if (= item nil)
      :no-stack-item
      item)))

(defn peek-stack-nth
  "Returns top item on a stack. If stack is empty, returns :no-stack-item"
  [state stack n]
  (let [item (nth (state stack) n nil)]
    (if (= item nil)
      :no-stack-item
      item)))

(defn get-entire-stack
  "Takes in a push state and a stack then returns all the arguments on the
   desired stack. If there are no items on the stack, returns :no-stack-item"
  [state stack]
  (loop [stack-items '()
         state state]
    (if (= (peek-stack state stack) :no-stack-item)
      ;; conj adds to beginning so to preserve stack order reverse resultant list
      (reverse stack-items)
      (recur (conj stack-items (peek-stack state stack))
             (pop-stack state stack)))))

(defn empty-stack?
  "Returns true if the stack is empty in state, else False"
  [state stack]
  (if (empty? (state stack))
    true
    false))

(defn get-args-from-stacks
  "Takes a state and a list of stacks to take args from. If there are enough args
  on each of the desired stacks, returns a map with keys {:state :args}, where
  :state is the new state with args popped, and :args is a list of args from
  the stacks. If there aren't enough args on the stacks, returns :not-enough-args."
  [state stacks]
  (loop [state state
         stacks (reverse stacks)
         args '()]
    (if (empty? stacks)
      {:state state :args args}
      (let [stack (first stacks)]
        (if (empty-stack? state stack)
          :not-enough-args
          (recur (pop-stack state stack)
                 (rest stacks)
                 (conj args (peek-stack state stack))))))))

(defn make-push-instruction
  "A utility function for making Push instructions. Takes a state, the function
  to apply to the args, the stacks to take the args from, and the stack to return
  the result to. Applies the function to the args (taken from the stacks) and pushes
  the return value onto return-stack in the resulting state."
  [state function arg-stacks return-stack]
  (let [args-pop-result (get-args-from-stacks state arg-stacks)]
    (if (= args-pop-result :not-enough-args)
      state
      (let [result (apply function (:args args-pop-result))
            new-state (:state args-pop-result)]
        (push-to-stack new-state return-stack result)))))

;;;;;;;;;
;; Instructions

(defn exec_dup
  "Duplicates the top instruction on the exec stack to the top of the exec stack.
   If the exec stack is empty, nothing is done."
  [state]
  (if (empty-stack? state :exec)
    state
    (push-to-stack state :exec (first (:exec state)))))

;;;;;;;;
;; Q-gate instructions

(defn all-distinct?
  "Takes in a list of arguments and verifies that all arguments are distinct.
   In addition, it checks that :no-stack-item is not one of the arguments
   sent to account for checking arguments from a stack that are not there.
   If all-distinct, returns true, else false"
  [& args]
  (if (empty? (filter #(= % :no-stack-item) args))
    (apply distinct? args)
    false))

(defn not_helper
  "Helper function for qgate_not that takes in 1 distinct integer,
   the qubit to apply the not gate to."
  [arg1]
  (qgate/translate-qgate-tensor-product qgate/not-gate arg1))

(defn qgate_not
  "Implements the not gate which flips the state of a qubit
   From state, 1 integer is taken from the integer stack corresponding to 
   the qubit to apply the gate to."
  [state]
  (make-push-instruction state not_helper [:integer] :qgate))

(defn haddamard_helper
  "Helper function for qgate_haddamard that takes in 1 distinct integer,
   the qubit to apply the haddamard gate to."
  [arg1]
  (qgate/translate-qgate-tensor-product qgate/haddamard-gate arg1))

(defn qgate_haddamard
  "Implements the haddamard gate which puts a qubit into a superposition
   of two states.
   From state, 1 integer is taken from the integer stack corresponding to 
   the qubit to apply the gate to."
  [state]
  (make-push-instruction state haddamard_helper [:integer] :qgate))

(defn controlled_z_helper
  "Helper function for qgate_controlled_z that takes in 2 distinct integers,
   the qubits to apply the controlled z to."
  [arg1 arg2]
  (qgate/translate-qgate-tensor-product qgate/controlled-z-gate arg1 arg2))

(defn qgate_controlled_z
  "Implements the controlled Z gate that operates on a pair of qubits, with 
   one qubit acting as the control and the other as the target. The CZ gate 
   applies a phase flip (change in the relative phase) to the target qubit 
   only when the control qubit is in the state |1⟩. If the control qubit is 
   in the state |0⟩ the CZ gate does not affect the target qubit.
   From state, 2 integers are taken from the integer stack corresponding to 
   the qubits to apply the gate to.
   Description came from: https://www.sharetechnote.com/html/QC/QuantumComputing_Gate_cZ.html"
  [state]
  (let [args (map #(peek-stack-nth state :integer %) (range 2))]
    (if (apply all-distinct? args)
      (make-push-instruction state controlled_z_helper [:integer :integer] :qgate)
      state)))

(defn cnot_helper
  "Helper function for qgate_cnot that takes in 2 distinct integers, the
  qubits to swap the states of."
  [arg1 arg2]
  (qgate/translate-qgate-tensor-product qgate/cnot-gate arg1 arg2))

(defn qgate_cnot
  "Implements the controlled NOT gate (or CNOT or CX) acts on 2 qubits,
   and performs the NOT operation on the second qubit only when the state
   of the first qubit is |1>, and otherwise leaves it unchanged.
   From state, 2 integers are taken from the integer stack corresponding to 
   the qubits to apply the gate to."
  [state]
  (let [args (map #(peek-stack-nth state :integer %) (range 2))]
    (if (apply all-distinct? args)
      (make-push-instruction state cnot_helper [:integer :integer] :qgate)
      state)))

(defn swap_helper
  "Helper function for qgate_swap that takes in 2 distinct integers, the
   qubits to swap the states of."
  [arg1 arg2]
  (qgate/translate-qgate-tensor-product qgate/swap-gate arg1 arg2))

(defn qgate_swap
  "Implements the swap quantum gate, that swaps the states of two qubits.
   Takes in as input, state, the state of the program to apply gate to.
   From state, 2 integers are taken from the integer stack corresponding to 
   the qubits to apply the gate to."
  [state]
  (let [args (map #(peek-stack-nth state :integer %) (range 2))] ;; Top 2 integers on integer stack
    (if (apply all-distinct? args) ;; Verify there were 2 integers and they were distinct.
      (make-push-instruction state swap_helper [:integer :integer] :qgate)
      state)))

(defn toffoli_helper
  "Helper function for qgate_toffoli that takes in 3 distinct integers, the qubits
   to apply the gate to."
  [arg1 arg2 arg3]
  (qgate/translate-qgate-tensor-product qgate/toffoli-gate arg1 arg2 arg3))

(defn qgate_toffoli
  "Implements the toffoli quantum gate, also known as the 'controlled-controlled-not' gate,
   which describes its action. It has 3-bit inputs and outputs; if the first two bits are 
   both set to 1, it inverts the third bit, otherwise all bits stay the same.
   Takes in as input, state, the state of the program to apply gate to.
   From state, 3 integers are taken from the integer stack corresponding to the qubits to
   apply the gate to."
  [state]
  (let [args (map #(peek-stack-nth state :integer %) (range 3))]
    (if (apply all-distinct? args) ;; Verify there were 3 integers and they were distinct.
      (make-push-instruction state toffoli_helper [:integer :integer :integer] :qgate)
      state)))

;;;;;;;;;
;; Interpreter
(defn unwrap-program-onto-exec
  "Takes in a state and program and 'unwraps' the program by pushing each of its
   elements onto the exec stack such that the first program element will be on the
   top of the exec stack and the last element will be at the bottom of the stack
   so that the program can be processed."
  [state program]
  (loop [program (reverse program)
         state state]
    (if (empty? program)
      state
      (recur (rest program)
             (push-to-stack state :exec (first program))))))

(defn is-literal?
  "Checks if an item is a literal. True if literal, else false"
  [item]
  (if (or (int? item) (m/matrix? item))
    true
    false))

(defn is-genome?
  "checks if an item is a genome. True if genome, else false"
  [item]
  (if (list? item)
    true
    false))

(defn item-to-keyword
  "Takes in an item and if it is an integer or string a keyword is
   returned for the appropiate stack to push the item onto. If the
   item is not one of our stacks an error message is printed in honor
   of the countless hours this evil function took from me (for debugging purposes)."
  [item]
  (cond
    (int? item) :integer
    (m/matrix? item) :qgate
    :else "Painful error that has taken countless hours of my life."))

(defn interpret-one-step
  "Helper function for interpret-push-program.
  Takes a Push state and executes the next instruction on the exec stack,
  or if the next element is a literal, pushes it onto the correct stack.
  Or, if the next element is a nested list, needs to unwrap that list onto
  the exec stack.
  Returns the new Push state."
  [push-state]
  (let [item (first (push-state :exec))
        state (pop-stack push-state :exec)]
    (cond
      (is-literal? item) (push-to-stack state (item-to-keyword item) item)
      (is-genome? item) (unwrap-program-onto-exec state item)
      :else ((eval item) state))))

;; A step-limit for how many evaluations steps to make on a program before quitting
(def step-limit 500)

(defn interpret-push-program
  "Runs the given program starting with the stacks in start-state. Continues
  until the exec stack is empty. Returns the state of the stacks after the
  program finishes executing.
   To avoid infinite execution, you will need to enforce some maximum number
  of interpreter steps before terminating the program. You can choose this limit."
  [program start-state]
  (loop [state (unwrap-program-onto-exec start-state program) ;; put program onto the exec stack for evaluation
         step 0]
    (if (or (empty? (state :exec)) (= step step-limit)) ;; stop when exec stack empty or step limit reached
      state
      (recur (interpret-one-step state)
             (inc step)))))


;;;;;;;;;
;; Translation from Plushy genomes to Push programs

(defn translate-plushy-to-push
  "Returns the Push program expressed by the given plushy representation."
  [plushy]
  (let [opener? #(and (vector? %) (= (first %) 'open))] ;; [open <n>] marks opened-blocks
    (loop [push () ;; iteratively build the Push program from the plushy
           plushy (mapcat #(if-let [n (get opened-blocks %)] [% ['open n]] [%]) plushy)]
      (if (empty? plushy)       ;; maybe we're done?
        (if (some opener? push) ;; done with plushy, but unclosed open
          (recur push '(close)) ;; recur with one more close
          push)                 ;; otherwise, really done, return push
        (let [i (first plushy)]
          (if (= i 'close)
            (if (some opener? push) ;; process a close when there's an open
              (recur (let [post-open (reverse (take-while (comp not opener?)
                                                          (reverse push)))
                           open-index (- (count push) (count post-open) 1)
                           num-open (second (nth push open-index))
                           pre-open (take open-index push)]
                       (if (= 1 num-open)
                         (concat pre-open [post-open])
                         (concat pre-open [post-open ['open (dec num-open)]])))
                     (rest plushy))
              (recur push (rest plushy))) ;; unmatched close, ignore
            (recur (concat push [i]) (rest plushy)))))))) ;; anything else


;;;;;;;;;
;; GP

;; Below are some values to use for controlling some aspects of GP runs

;; A GP parameter to control the size of tournaments
(def tournament-size 5)

;; Value to use for 50-50 probability decisions -> 50%
(def coin-flip-prob 0.5)

;; Sets the mutation rate - currently set to 20%
(def mutation-rate 0.2)

;; Sets the number of individuals to pick for trying to find a subsequence of qgates
(def n-subsequence-inds 50)

;; Sets how many generations it takes till a subsequence of qgate is picked to be composed
(def n-generation-compose 40)

(defn compose-helper
  "Takes in a population of individuals and returns n-subsequence-inds random
   individuals."
  [population]
  (loop [random-individuals []
         reduced-population (shuffle population)]
    (if (or (= (count random-individuals) n-subsequence-inds)
            (= (count random-individuals) (count population)))
      random-individuals
      (recur (conj random-individuals (first reduced-population))
             (rest reduced-population)))))


(defn compose-qgate
  "Takes in an errro-evaluated population and picks some subset of the population.
   From this subset, the individual with the lowest error is picked and a subsequence
   of quantum gates of arbitrary size is composed into one quantum gate, matrix, that
   is added to the instruction set as a terminal to be added into programs."
  [error-evaluated-population] 
        ;; Pick random individuals for getting a subseqeunce of qgates.
  (let [random-individuals (compose-helper error-evaluated-population)
        ;; Take the best individual from the random set
        best-ind (apply min-key :total-error random-individuals)
        ;; Interpret the individual's program and grab the qgate stack
        qgate-stack  (apply vector ((interpret-push-program (best-ind :program) empty-push-state) :qgate))
        ;; Pick a random index within the qgate stack to start subseqeunce from
        random-index (rand-int (count qgate-stack))
        ;; Choose a random length for the subsequence (inc is so that if 0 is picked at least one gate will be returned)
        random-length (inc (rand-int (- (count qgate-stack) random-index)))
        ;; Create the subsequence
        subseq (if (empty? qgate-stack)
                 nil
                 (m/subvector qgate-stack random-index random-length))]
    ;; If only one qgate in the subsequence return it, else compose subsequence into one gate
    (if (= (count subseq) 1)
      (first subseq)
      (reduce #(m/mmul %1 %2) subseq))))

(defn make-random-plushy-genome
  "Creates and returns a new plushy genome. Takes a list of instructions and
  a maximum initial Plushy genome size."
  [instructions max-initial-plushy-size]
  (let [num_instructions (inc (rand-int max-initial-plushy-size))]
    (take num_instructions (repeatedly #(rand-nth instructions)))))

(defn select-random-and-remove
  "Helper for tournament selection that returns a list of size tournament-size by 
   randomly picking an individual from population, removing that individual, and 
   picking a new random individual until (tournament-size) individuals have been picked."
  [population]
  (loop [population (shuffle population)
         random-population '()]
    (if (= (count random-population) tournament-size)
      random-population

      ;; shuffle population so we can pick random individual by grabbing first element
      (recur (shuffle (rest population))
             (conj random-population (first population))))))

(defn tournament-selection
  "Selects an individual from the population using a tournament. Returned
  individual will be a parent in the next generation. Can use a fixed
  tournament size."
  [population]
  (let [random-population (select-random-and-remove population)]
    (apply min-key :total-error random-population))) ;; Parent to return is one with lowest total-error

(defn pick-random-elem
  "Helper function for picking which element to pick between programs in crossover.
   Takes two elements, elem-a and elem-b, and flips a coin to choose which element to return."
  [elem-a elem-b]
  (let [prob (rand)]
    (if (< prob coin-flip-prob)
      elem-a
      elem-b)))

(defn return-end-of-longer
  "Helper function for crossover that allows for elements to be crossed over from two
   programs of differnet length by returning the end of the longer program.
   Takes in two programs, prog-a and prog-b, and returns the end of the longer program."
  [prog-a prog-b]
  (let [diff (abs (- (count prog-a) (count prog-b)))]
    (if (> (count prog-a) (count prog-b))
      (take-last diff prog-a)
      (take-last diff prog-b))))

(defn select-elems-probability
  "Helper function for crossover that takes the end of a longer program and chooses
   which element to keep for frossover by flipping a coin for each element."
  [seq]
  (loop [seq seq
         prob-seq '()
         prob (rand)]
    (if (empty? seq)
        ;; Programs are stored in a list and conj will build this backwards
        ;; so we need to reverse the result
      (reverse prob-seq)
      (recur (rest seq)
             (if (< prob coin-flip-prob)
               (conj prob-seq (first seq))
               prob-seq)
             (rand)))))

(defn crossover
  "Crosses over two Plushy genomes (note: not individuals) using uniform crossover.
  Returns child Plushy genome."
  [prog-a prog-b]
  (let [partial-child (map #(pick-random-elem %1 %2) prog-a prog-b)
        end-longer-prog (return-end-of-longer prog-a prog-b)]
    (concat partial-child (select-elems-probability end-longer-prog))))

(defn make-uniform-addition-subseq
  "Helper function for uniform-addition that takes the instruction set and current
   element to (potentially) add a random instruction before current element"
  [instructions elem]
  (let [rand-instruct (rand-nth instructions)
        subseq '()]
    (if (< mutation-rate (rand)) ;; if we win the probability spin
      (conj subseq elem) ;; no mutation -> return element in list to be concatted in uniform-addition
      (conj (conj subseq elem) rand-instruct)))) ;; places the random instruction before original element

(defn uniform-addition
  "Randomly adds new instructions before every instruction (and at the end of
  the Plushy genomes) with some probability. Returns child Plushy genome."
  [prog instructions]
  (loop [current-prog prog
         resultant-prog '()]
    (if (empty? current-prog)
      ;; Handles adding an addition to the end of our genome with some probability
      (if (< mutation-rate (rand))
        resultant-prog
        ;; Add an element to the end of resultant-prog by stuffing an element in a list and concatting
        ;; to the end of the list. This saves playing games with conj adding to the beginning of a list.
        (concat resultant-prog (conj '() (rand-nth instructions))))
      (recur (rest current-prog)
             (concat resultant-prog
                     (make-uniform-addition-subseq instructions (first current-prog)))))))

(defn uniform-deletion
  "Randomly deletes instructions from Plushy genomes at some rate. Returns
   child Plushy genome."
  [prog]
  (loop [current-prog prog
         resultant-prog '()]
    (if (empty? current-prog)
      (reverse resultant-prog) ;; I loop through conjing a new list together so result should be reversed
      (recur (rest current-prog)
             (if (< mutation-rate (rand))
               (conj resultant-prog (first current-prog))
               resultant-prog)))))

(defn select-and-vary
  "Selects parent(s) from population and varies them, returning
  a child individual (note: not program/genome). Chooses which genetic operator
  to use probabilistically. Gives 50% chance to crossover,
  25% to uniform-addition, and 20% to uniform-deletion."
  [population instructions]
  (let [prob (rand)
        ind1 (tournament-selection population)
        ind2 (tournament-selection population)]
    (cond
      ;; Perform variation with probability and update individual's genome
      (<= prob 0.25) (assoc ind1 :genome (uniform-addition (ind1 :genome) instructions)) ;; 30% chance to perform uniform-addition
      (<= prob 0.5) (assoc ind1 :genome (uniform-deletion (ind1 :genome))) ;; 20% chance to perform uniform-deletion
      :else (assoc ind1 :genome (crossover (ind1 :genome) (ind2 :genome)))))) ;; 50% chance to perform crossover

(defn report
  "Reports information on the population each generation. Should look something
  like the following (should contain all of this info; format however you think
  looks best; feel free to include other info).

-------------------------------------------------------
               Report for Generation 3
-------------------------------------------------------
Best program: (in1 integer_% integer_* integer_- 0 1 in1 1 integer_* 0 integer_* 1 in1 integer_* integer_- in1 integer_% integer_% 0 integer_+ in1 integer_* integer_- in1 in1 integer_* integer_+ integer_* in1 integer_- integer_* 1 integer_%)
Best program size: 33
Best total error: 727
Best errors: (117 96 77 60 45 32 21 12 5 0 3 4 3 0 5 12 21 32 45 60 77)
  "
  [best-individual best-individual-run generation training-cases]
  (println "-------------------------------------------------------")
  (println "               Report for Generation" generation)
  (println "-------------------------------------------------------")
  (println "Best individual in current run:" best-individual-run)
  (println "Best individual in current run error:" (best-individual-run :total-error))
  (println "Best individual:" best-individual)
  (println "Best program size:" (count (best-individual :genome)))
  (println "Best total error:" (best-individual :total-error))
  (println "Best errors:" (best-individual :errors))
  (println "Training cases:" training-cases))

(defn make-random-individual
  "Takes in an instruction set and a max size of program to generate then creates
   a random individual with errors set to empty vector and 0 respectively."
  [instructions max-initial-plushy-size]
  (let [plushy-genome (make-random-plushy-genome instructions max-initial-plushy-size)]
    {:genome plushy-genome
     :program (translate-plushy-to-push plushy-genome)
     :errors []
     :total-error 0}))

(defn generate-random-population
  "Takes in the size of population to generate, the instructions to use in program creation,
   and the max size of programs to generate to create a population of programs."
  [population-size instructions max-initial-plushy-size]
  (loop [population '()]
    (if (= (count population) population-size)
      population
      (recur (conj population (make-random-individual instructions max-initial-plushy-size))))))

(defn push-gp
  "Main GP loop. Initializes the population, and then repeatedly
  generates and evaluates new populations. Stops if it finds an
  individual with 0 error (and should return :SUCCESS, or if it
  exceeds the maximum generations (and should return nil). Should print
  report each generation.
  --
  The only argument should be a map containing the core parameters to
  push-gp. The format given below will decompose this map into individual
  arguments. These arguments should include:
   - population-size
   - max-generations
   - error-function
   - instructions (a list of instructions)
   - max-initial-plushy-size (max size of randomly generated Plushy genomes)"
  [{:keys [population-size max-generations error-function instructions max-initial-plushy-size training-cases use-compose]
    :as argmap}]
  ;; Begin by generating a random population and initializing generation to 0
  (loop [current-instructions instructions
         population (generate-random-population population-size current-instructions max-initial-plushy-size)
         generation 0
         best-ind-run (assoc (first population) :total-error ##Inf)]

    ;; Now, take the current population and update each individual's error by mapping over
    ;; the population and applying the error function to each individual
    (let [evaluated-error-population (map #(error-function % training-cases) population)
          best-ind (apply min-key :total-error evaluated-error-population)]  ;; best-ind has lowest total-error
      (report best-ind best-ind-run generation training-cases)

      ;; Handles evolution termination / creation of next generation
      (cond
        (= (best-ind :total-error) 0) :SUCCESS
        (= generation max-generations) (if (< (best-ind :total-error) (best-ind-run :total-error))
                                         [best-ind training-cases]
                                         [best-ind-run training-cases])
        
        ;; If use-compose instruction is true, use it, else use default instruction set
        :else (recur (if use-compose
        ;; Every n generations, compose a subsequence of qgate into the instruction set
                       (if (= (mod generation n-generation-compose) 0)
                         (let [composed-instruction (compose-qgate evaluated-error-population)]
                           (if (m/matrix? composed-instruction) ;; Check that a subsequence was returned
                             (conj current-instructions composed-instruction) ;; Add to instruction set
                             current-instructions))
                         current-instructions)
                       current-instructions)
        ;; Map over the new population and update the programs according to the genome generated in select-and-vary
                     (map #(assoc % :program (translate-plushy-to-push (% :genome)))
        ;; The list to map over is the new population generated by performing parent selection and varying the current one
                          (repeatedly population-size #(select-and-vary evaluated-error-population current-instructions)))
                     (inc generation)
                     (if (< (best-ind :total-error) (best-ind-run :total-error))
                       best-ind
                       best-ind-run))))))
                       
;;;;;;;;;;
;; Quantum PF Max Error Function
;; The functions below are specific to the PF Max problem
;; Problem: Given ANY permutation function f(x) that is supplied as input
;; and which operates on the integer range [0..3], use a suitable encoding
;; to evolve a quantum program, U, that returns the value of x that gives
;; the maximum value of f(x).

;; A constant to divide numGates by to decentivize solutions with many quantum gates that may introduce rounding errors
(def empirical-efficiency-constant 100000000)
;; Probability needed for a state to be 'correct' - greater than 0.51 to account for rounding errors
(def rounding-adjusted-prob 0.52)
;; For use in determining correctness of a state -> if we measure an error greater than this consider the error
(def correctness-threshold (- 1 rounding-adjusted-prob))
;; General probability to initialize state elements to for an n qubit system
(def state-prob (double (/ 1 (math/sqrt (bit-shift-left 1 qgate/n-input-qubits)))))

(defn make-input-permutations
  "Takes in an integer n, and generates all permuations of (range n)"
  [n]
  (combo/permutations (range n)))

(defn make-quantum-training-cases
  "Takes in an integer, n, and generates n random training cases expressed as permutations
   of [0 1 2 3]"
  [n]
  (loop [random-cases '()
         ;; Make input permutations representing the desired state for each qubit
         cases (shuffle (make-input-permutations qgate/n-qubits))]
    (if (= (count random-cases) n)
      random-cases
      (recur (conj random-cases (first cases))
             (shuffle (rest cases))))))

(defn make-input-state-vector
  "Takes in a fitness case expressed as a permutation of [0 1 2 3] and encodes
   the permutation in a quantum state expressed as a vector of size, 2^(size permutation)
   where all elements are zero except for the encoding of the permutation - whose elements
   are all given equal probability to be measured, 0.5
   To encode the state, if the permutation is [3 1 2 0] then the encoding would be,
    f(0) = 3    f(1) = 1    f(2) = 2    f(3) = 0
   [0 0 0 0.5 | 0 0.5 0 0 | 0 0 0.5 0 | 0.5 0 0 0]"
  [permutation]
  (let [len-permutation (count permutation)]
    (loop [state-vec (qgate/length-n-vec (bit-shift-left 1 (count permutation)))
           permutation permutation
           index 0]
      (if (empty? permutation)
        state-vec
        (recur (m/mset state-vec (+ (* index len-permutation) (first permutation)) state-prob)
               (rest permutation)
               (inc index))))))

(defn state-prob-x
  "Takes in a quantum state, state, and a desired integer input value within that state then determines
   the probability that the input x is what we measure when the system is observed."
  [state x]
  (let [probs-x (m/subvector state (* x (bit-shift-left 1 qgate/n-input-qubits)) qgate/n-qubits)]
    (apply + (map #(math/expt % 2) probs-x))))

(defn state-prob-xs
  "Returns a seq of the probability to measure each possible input 
   value, x, from a quantum state, state."
  [state]
  (map #(state-prob-x state %) (range qgate/n-qubits)))

(defn correct-answer?
  "Takes in a fitness case and the resultant probability to measure (x = 0, 1, 2, 3)
   for fitness case. If the correct input (the one that maximizes fitness-case) has
   a probability greater than 0.52 return 1, else 0."
  [fitness-case state-probs]
  (reduce + (map (fn [value prob]
                   (if (and (> prob rounding-adjusted-prob)
                            ;; Value that maximizes f(x) is max value we can represent,
                            ;; 2^nInputQubits
                            (= value (dec (bit-shift-left 1 qgate/n-input-qubits))))
                     1 0))
                 fitness-case state-probs)))

(defn get-hits
  "Takes in the fitness cases being tested and the resultant probabilities to measure (x = 0, 1, 2, 3)
   for each case. A hit occurs when the probability to measure the input that maximizes an arbitrary
   function f(x) is greater than 0.52.
   hits = numTrainingCases - numCorrect"
  [fitness-cases state-probs]
  (- (count fitness-cases) (reduce + (map #(correct-answer? %1 %2) fitness-cases state-probs))))

(defn get-error-case
  "Takes in a fitness case and the probability to measure (x = 0, 1, 2, 3). From this,
   the magnitude of the error (the probability to measure the inputs that don't correspond
   to the max value in the fitness case) is calculated and returned."
  [fitness-case state-prob]
       ;; Deletion index is the index of the value that maximizes an arbitrary function, f(x).
       ;; Because half of our qubits encode the input and half the output the max value that
       ;; can be represented is 2^inputQubits
  (let [deletion-index (.indexOf fitness-case (dec (bit-shift-left 1 qgate/n-input-qubits)))
        error-vec (m/join (m/subvector state-prob 0 deletion-index)
                          (m/subvector state-prob (inc deletion-index) (- (dec (count state-prob)) deletion-index)))]
    (apply + error-vec)))

(defn get-correctness
  "Takes in fitness cases, the probability to measure each input of fitness cases, and
   the number of hits.
   From this, the  size of the error on each case is quantified and returned.
   correctness = (sum_trainingCases (max 0, error_case)) / max(hits, 1)"
  [fitness-cases state-probs hits]
       ;; Sum over training cases, getting the magnitude of the error for each case
  (let [case-errors (map #(get-error-case %1 %2) fitness-cases state-probs)]
    (/ (apply + (map #(max 0 (- % correctness-threshold)) case-errors))
       (max 1 hits))))

(defn q-fitness-evaulation
  "Takes in an individual and fitness cases to test it upon and performs a
   probabilistic error function defines as,
   fitness = hits + correctness + efficiency; where, 
   - hits is defined as the total number of fitness cases used minus the number
     of fitness cases where the program produces the correct answer with a 
     probability greater than 0.52 to account for rounding errors in programs.
   - correctness is defined to be the sum over all training cases where for
     each training case the element summed is the max of 0 or the total error
     for the case, quantity divided by the max of hits or 1,
     correctness = (sum_trainingCases (max 0, error_case)) / max(hits, 1)
   - Efficiency is the number of quantum gates used in a candidate program
     divided by a large empirical constant to encourage solutions with
     fewer gates,
     efficiency = numGate / BIGNUMBER"
  [individual fitness-cases]
  (let [;; Fitness cases are expressed as permutations of [0 1 2 3] -> encode problem into a quantum state
        q-states (map #(make-input-state-vector %) fitness-cases)
        ;; Return the resultant state of evaluating an individual's program
        resultant-state (interpret-push-program
                         (individual :program)
                         empty-push-state)
        ;; Candidate program is the matrices stored on the qgate stack
        candidate-program (get-entire-stack resultant-state :qgate)]
    ;; If there are no matrices on the qgate stack return an infinite error, else process canddiate program
    (if (empty? candidate-program)
      (assoc individual :total-error ##Inf)

      ;; Reduce stack of matrices into one candidate program, matrix, to apply to q-state
      (let [reduced-candidate-program (if (> (count candidate-program) 1)
                                        (reduce #(m/mmul %1 %2) candidate-program)
      ;; If only one matrix grab it with 'first' otherwise sad data structure errors occur
                                        (first candidate-program))
            ;; Apply candidate program to all of the quantum states, training cases, being tested
            evaluated-q-states (map #(m/mmul reduced-candidate-program %) q-states)
            ;; Return the probability to measure each input in the system (x = 0, 1, 2, 3) for all q-states
            state-probs (map #(state-prob-xs %) evaluated-q-states)
            ;; Determine hits by checking if the correct input has a prob > 0.52 for all fitness cases 
            hits (get-hits fitness-cases state-probs)
            ;; Correctness gives a penalty for training cases that haven't been solved proportionate to
            ;; the size of the error on the case
            correctness (get-correctness fitness-cases state-probs hits)
            ;; Determine efficiency by dividing numGate / empirical-efficiency-constant
            efficiency (/ (count candidate-program) empirical-efficiency-constant)]
        ;; Update an individual's total error
        (assoc individual :total-error (+ hits correctness efficiency))))))

;;;;;;;;;;
;; The main function call
;; You can call this in a REPL, or alternatively from the command line
;; by running:
;;   clj -X push411.core/main
;; Additionally, if you want to pass command line arguments as a map to args,
;; you can run something like:
;;   clj -X push411.core/main :selection :lexicase
(defn main
  "Runs push-gp, giving it a map of arguments."
  ([] (main {}))
  ([args]
   (push-gp {:instructions default-instructions
             :error-function q-fitness-evaulation
             :max-generations 500
             :population-size 250
             :max-initial-plushy-size 60
             :training-cases (make-quantum-training-cases 8)
             :use-compose true}))) ;; option for using novel compose instruction
(comment
  ;; No arguments
  (main)

  ;; x runs
  (take 3 (repeatedly main))

  ;; Use args as a map
  (main {:selection :lexicase}))

;; Finally, this is finished.