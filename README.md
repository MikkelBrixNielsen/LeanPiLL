# LeanPiLL 💊
## Formalizing the Curry-Howard Correspondence for Concurrency in Lean 4
LeanPiLL is an MSc project focused on using Lean 4 to create a machine-checked formalization of the relation between Linear Logic, the π-calculus, and Session Types.

# Project Scope
This formalization follows the "Proofs as Processes" paradigm using Montesi and Peressotti [1] as inspiration. The current development focuses on developing the definition of the theoretical framework for relating linear logic proofs to concurrenct processes.

## Core Objectives
- Model: Define the syntax for concurrent processes and linear session types.
- Semantics: Implement the structural and dynamic relations.
- Substitution: Verify the substitution lemmas required for reduction.  
- Session Fidelity: Verify the mathematical consistency of the framework

# Repository Structure
- PiLL/
  - Model/: Contains the core definitions, syntax and substitution proofs.
  - Semantics/: Contains the inductive step relations.
  - SessionFidelity/: Session fidelity proofs.

# References
[1] Fabrizio Montesi and Marco Peressotti. Linear logic, the π-calculus, and their metatheory: A recipe for proofs as processes. CoRR, abs/2106.11818, 2021.
