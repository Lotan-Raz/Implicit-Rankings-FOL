# Implicit-Rankings-FOL
Implementation for the paper: "Implicit Rankings for Verifying Liveness Properties in First-Order Logic"

Requirements: Z3 installed

In file ts we have the classes with which you can encode states, transition systems, implicit rankings, liveness properties and liveness proofs.
Every other file is an example, every example consists of defining a transition system, a liveness property, and a liveness proof which includes the definition of a suitable implicit ranking given the implicit ranking constructors.
To verify an example, run the corresponding python file. 

The file Empty can be used as a template for defining new examples.

The files TrivialTermination_Empty is an exercise for interested users that want to try and find an implicit ranking for an easy example on their own, the solution appears in  TrivialTermination_Full
