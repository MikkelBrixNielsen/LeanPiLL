# LeanPiLL 💊

## Formalising πLL in Lean 4

LeanPiLL is the Lean 4 development accompanying the MSc thesis *Formalising πLL in Lean*. It mechanises the process calculus and metatheoretic framework developed by Montesi and Peressotti, relating linear logic, the π-calculus, and session-typed communication.

## Scope

The development formalises the static structure of the full πLL calculus, including:

* session types and duality;
* processes and binding operations;
* environments and hyperenvironments;
* typing judgements;
* name and type substitution principles.

The operational semantics and session-fidelity development currently target the multiplicative fragment, πMLL. The formalisation defines:

* a derivation-level typed transition system;
* a projected process-level transition system;
* a projected hyperenvironment transition system.

The completed metatheory establishes the projection of typed transitions to process and resource transitions and develops the reverse lifting argument for the multiplicative transition cases except `res`. The remaining proof obligation is the reconstruction of the endpoint-bearing hyperenvironment components required to rebuild `cut` after a transition beneath restriction.

## Binding Representation

The formalisation retains explicit free identifiers while representing bound occurrences by indices.

* Process channel binders use a locally nameless representation with opening, closing, local closure, and co-finite typing premises.
* Polymorphic type binders use type-depth indexing, shifting, local closure, and substitution.

This representation avoids explicit reasoning up to α-equivalence for bound occurrences, while making freshness and resource-reconstruction obligations explicit in Lean.

## Repository Structure

```text
PiLL/
├── Model/             Static syntax, environments, typing judgements,
│                      binding infrastructure, and substitution lemmas
├── Semantics/         Typed, process-level, and environment-level
│                      transition relations
└── SessionFidelity/   Projection, lifting, and session-fidelity proofs
```

## Build

The development can be checked with:

```bash
lake build
```

## Current Status

* Static formalisation of full πLL: implemented.
* Operational semantics for πMLL: implemented.
* Typed-to-process and typed-to-environment projection results: implemented.
* Reverse lifting / typability result for πMLL: complete except for the `res` case.
* Full πLL operational semantics and broader behavioural metatheory: future work.

## Reference

[1] Fabrizio Montesi and Marco Peressotti. *Linear logic, the π-calculus, and their metatheory: A recipe for proofs as processes*. CoRR, abs/2106.11818, 2021.
