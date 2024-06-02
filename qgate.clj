(ns push411.qgate
  (:require [clojure.math.numeric-tower :as math] 
            [clojure.core.matrix :as m]
            [push411.complex :as complex]
            ))

(comment
  "Implements a set of functions that allow for the construction of quantum gates
   to be applied to quantum states of n-qubits and for the application of these
   gates to any qubit in a quantum state.")

;;
;; MAGIC NUMBERS
;;

(def n-qubits 4)
(def n-input-qubits 2)
;;
;; QUANTUM STATES
;;

;; Defines spin-up (also could be called the |+> state)
(def spin-up [0 1])

;; Defines spin-down (also could be called the |-> state)
(def spin-down [1 0])

;;
;; QUANTUM GATES
;;

;; Imlements the identity-gate matrix,
;;    This is a one qubit gate that doesn't change the state of a qubit
(def i-gate (m/matrix [[1 0]
                       [0 1]]))

;; Implements the 1-qubit not-gate,
;;    This gate inverts the state of a qubit
(def not-gate (m/matrix [[0 1]
                         [1 0]]))

;; Implements the 1-qubit haddamard-gate,
;;    This gate puts a qubit into a superposition of two quantum states. 
(def haddamard-gate (m/mul (/ 1 (math/sqrt 2)) (m/matrix [[1 1]
                                                          [1 -1]])))

;; Implements the 2-qubit controlled-z-gate
;;    This gate uses one qubit acting as the control and the other as the target. 
;;    The CZ gate applies a phase flip (change in the relative phase) to the target qubit 
;;    only when the control qubit is in the state |1⟩. If the control qubit is 
;;    in the state |0⟩ the CZ gate does not affect the target qubit.
;;    Description came from: https://www.sharetechnote.com/html/QC/QuantumComputing_Gate_cZ.html
(def controlled-z-gate (m/matrix [[1 0 0 0]
                                 [0 1 0 0]
                                 [0 0 1 0]
                                 [0 0 0 -1]]))

;; Implements the 2-qubit CNOT-gate
;;    The controlled NOT gate (or CNOT or CX) acts on 2 qubits,
;;    and performs the NOT operation on the second qubit only when the state
;;    of the first qubit is |1>, and otherwise leaves it unchanged.
(def cnot-gate (m/matrix [[1 0 0 0]
                          [0 1 0 0]
                          [0 0 0 1]
                          [0 0 1 0]]))

;; Implements the 2-qubit swap-gate
;;    This gate swaps the states of two qubits.
(def swap-gate (m/matrix [[1 0 0 0]
                          [0 0 1 0]
                          [0 1 0 0]
                          [0 0 0 1]]))

;; Implements the 3-qubit toffoli-gate
;;    The toffoli quantum gate, also known as the 'controlled-controlled-not' gate,
;;    which describes its action. It has 3-bit inputs and outputs; if the first two bits are 
;;    both set to 1, it inverts the third bit, otherwise all bits stay the same.
(def toffoli-gate (m/matrix [[1 0 0 0 0 0 0 0]
                             [0 1 0 0 0 0 0 0]
                             [0 0 1 0 0 0 0 0]
                             [0 0 0 1 0 0 0 0]
                             [0 0 0 0 1 0 0 0]
                             [0 0 0 0 0 1 0 0]
                             [0 0 0 0 0 0 0 1]
                             [0 0 0 0 0 0 1 0]]))

;; CUSTOM HELPER FUNCTIONS

(defn print-matrix [m]
  (doseq [i (range (m/row-count m))]
    (doseq [j (range (m/column-count m))]
      (print (m/mget m i j) "\t"))
    (println)))

;; Cite: https://snipplr.com/view/65234/logarithm-with-base-2-log2
;; Description: Implements log base 2
(defn log2 [n]
  (int (/ (Math/log n) (Math/log 2))))

;;
;; LINEAR ALGEBRA UTILITY TOOLS
;;

(defn length-n-vec 
  "Makes a double precision array of length n where all entries are 0"
  [n]
  (m/array (repeat n 0)))

(defn basis-vec
  "Creates a basis vector of length N where the element at index n is
   the non-zero basis element"
  [N n]
  (let [vec (length-n-vec N)]
    (m/mset vec n 1)))

(defn n-qubit-basis-vec
  "Generates the set of basis vectors that make up an n-qubit system.
   The input, n, deterimines how may qubits are in the system."
  [n]
  (let [basis-vecs (take n (repeatedly #(length-n-vec n)))]
    (map-indexed (fn [idx vec] (m/mset vec idx 1)) basis-vecs)))

(defn get-row-matrices
  "Takes in a list of matrices and the amount of matrices to place
   in a given column. The list of matrices will be joined along their
   rows for length, num-cols, until the list of matrices is processed
   as a list of lists where each innner list defines the matrices along
   a given row. This allows for each inner list to be joined into long
   row matrices and then for these row matrices to be joined along their
   columns to form a composite matrix from many smaller matrices."
  [matrices num-cols]
  (loop [row-matrices []
         current-row []
         counter 0
         matrices matrices]
    (if (empty? matrices)
      (if (empty? current-row)
        row-matrices
        (conj row-matrices current-row))
      (let [updated-row (conj current-row (first matrices))
            updated-counter (inc counter)]
        ;; If we have joined all the matrices to define a row then begin
        ;; a new row, else keep joining along a row.
        (if (= updated-counter num-cols)
          (recur (conj row-matrices updated-row) 
                 [] 
                 0 
                 (rest matrices))
          (recur row-matrices 
                 updated-row 
                 updated-counter 
                 (rest matrices)))))))

(defn join-matrix-rows 
  "Takes in two matrices, m1 and m2, and joins them along their rows."
  [m1 m2]
  (m/matrix (map (fn [row1 row2] (vec (concat row1 row2)))
                 (m/rows m1)
                 (m/rows m2))))

(defn join-matrix-cols 
  "Takes in two matrices, m1 and m2, and joins them along their columns."
  [m1 m2]
  (m/transpose
   (m/matrix (map (fn [col1 col2] (vec (concat col1 col2)))
                  (m/columns m1)
                  (m/columns m2)))))

(defn tensor-product
  "Computes the tensor product of two matrices, m1 and m2.
   The tensor product provides a representation for the matrix
   multiplication of two matrices of arbitrary size such
   as the multiplication of a 2x2 and 4x4 matrix.
   The formal definition of the tensor product can be found
   here, https://en.wikipedia.org/wiki/Tensor_product"
  [m1 m2]
  (let [scalars (m/to-vector m1) ;; Cast m1 into a list of scalars
        ;; Create the sub-matrices to make up resultant matrix.
        ;; sub matrices are just m1 cast into a list of scalars multiplied by m2 for each scalar.
        inner-matrices (map #(m/mul % m2) scalars)
        ;; Join the appropriate sub-matrices along their rows
        matrix-rows (map #(reduce join-matrix-rows %)
                         (get-row-matrices inner-matrices (m/column-count m1)))]
    ;; Once we have rows of joined matrices, join these rows of matrices along their columns
    ;; to create one resultant matrix composed of all the sub-matrices
    (reduce join-matrix-cols matrix-rows)))

(defn tensor-product-args
  "Takes in an arbitrary amount of matrices as arguments and computes
   the tensor product of all these matrices."
  [& args]
  ;; Check that at least two matrices are provided to compute the tensor product
  (if (< (count args) 2)
    (first args)
    (reduce tensor-product args)))

(defn kronecker-product
  "Computes the kronecker product of two vectors, v1 and v2, which is 
   just every possible multiplication of the vector elements. A more
   formal defintion can be found here, https://en.wikipedia.org/wiki/Tensor_product
     The formal definition is defined for matrices so I'm just defining this for 1D
     matrices, vectors."
  [v1 v2]
  (apply m/join (map #(m/mul % v2) v1)))

(defn kronecker-product-args
  "Computes the kronecker product of an arbitrary amount of vectors provided
   as argument."
  [& args]
  (if (< (count args) 2)
    (first args)
    (reduce kronecker-product args)))

(defn int-to-binary-vec
  "Converts an integer to a binary vector of a given length."
  [num len]
  (vec (reverse (map #(bit-and 1 (bit-shift-right num %)) (range len)))))

(defn binary-permutations
  "Generates all binary permutations for vectors of length n."
  [n]
  (let [max-value (bit-shift-left 1 n)]   ;; Cheeky trick to calculate 2^n
    (map #(int-to-binary-vec % n) (range max-value))))

(defn vec-integer-to-qstate
  "Takes in a vector of integers composed of 0 and 1. 0 and 1 corresponds
   to the quantum states spin-up and spin-down, |+> and |->. If the vector
   element is 1 it is translated to spin-up, else spin-down."
  [vec-int]
  (map #(if (= % 1) spin-up spin-down) vec-int))

(defn transform-basis-vec
  "Takes in a vector composed of 0 and 1s, a binary permutation. The elements
   of this vector correspond to spin-up and spin-down quantum states that are then
   rearranged in the order of the vector, basis-order, an ordering of 0..(nQubits - 1)
   that describes how to reorder the quantum state defined by, binary permutation."
  [binary-permutation basis-order]
  (map #(nth binary-permutation %) basis-order))

(defn basis-transformation
  "Creates a transformation matrix in the basis defined by the vector, basis-order, an
   ordering of 0..(nQubits - 1) that defines how to translate to a basis in which qubits
   are ordered in the order described by basis-order."
  [basis-order]
        ;; Create the basis vectors that describe an n-qubit system
  (let [binary-permutation-states (binary-permutations n-qubits) 
        ;; Reorder all of the basis states in the order described by basis-order
        transformed-binary-states (map #(transform-basis-vec % basis-order) binary-permutation-states)]
    ;; Translate basis vectors expressed as binary permutations of 0 and 1 to vectors of spin-up and spin-down
    ;; column vectors then expand this into one resultant basis vector using the kronecker product
    (map #(apply kronecker-product-args %) (map #(vec-integer-to-qstate %) transformed-binary-states))))

(defn transform-matrix
  "Transforms a matrix using a list of kets defining the new basis.
   Note: To not break the rest of my code this only returns the real component of the transformed operator.
         This works because I only use quantum gates with real components to them so I don't lose information
         by throwing away the imaginary parts of matrices.
   The basis transformation of a quantum operator is defined by,
   let S = transformation matrix, S-dagger the hermetian transpose of transformation matrix,
       O = quantum operator (quantum gate)
   basis-transformed-operator = S x O x S-dagger"
  [matrix kets]
  (let [S (complex/complex (m/matrix kets))
        S-dagger (complex/hermitian-transpose S)] 
    (complex/real (m/mmul (m/mmul S matrix) S-dagger))))

(defn complete-subsequence
  "Takes in a subsequence of numbers in the range of n-qubits and adds whatever
   numbers are not in the subsequence to the end."
  [subsequence]
  (let [subseq-set (set subsequence)
        missing-elements (filter #(not (contains? subseq-set %)) (range n-qubits))]
    (vec (concat subsequence missing-elements))))

(defn translate-qgate-tensor-product
  "Takes in a quantum gate and qubit indices to apply the gate to and builds the appropriate
   tensor product representation to apply the quantum gate to an nqubit system."
  [qgate & qubit-indices]
        ;; Determine number of qubits a quantum gate is working on
  (let [num-qubits (log2 (m/row-count qgate))
        ;; Expand the quantum gate to apply to an n-qubit system
        tensor-product-gates (apply tensor-product-args 
                                    (concat [qgate] 
                                            (apply vector (take (- n-qubits num-qubits) (repeat i-gate)))))
        ;; Create the basis to transform the quantum gate to work on specific qubits in the n-qubit system
        new-basis (basis-transformation (complete-subsequence qubit-indices))]
    (transform-matrix tensor-product-gates new-basis)))