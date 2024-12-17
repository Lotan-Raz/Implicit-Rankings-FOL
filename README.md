# Implicit-Rankings-FOL
Implementation for the paper: "Implicit Rankings for Verifying Liveness Properties in First-Order Logic"

Requirements: Z3 installed

In file ts we have the classes with which you can encode states, transition systems, implicit rankings, liveness properties and liveness proofs.
Every other file is an example, every example consists of defining a transition system, a liveness property, and a liveness proof which includes the definition of a suitable implicit ranking given the implicit ranking constructors.
To verify an example, run the corresponding python file. 
