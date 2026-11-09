---
name: autocorrode-contract-proofs
description: Rules for proving contracts of uRust functions in AutoCorrode (crush_boot and crush_base, loops, specifications). Use together with isabelle-proof-development whenever you prove an AutoCorrode function contract.
---

# Proving AutoCorrode contracts

Follow the worked examples: `Micro_Rust_Examples/Showcase.thy`, `Micro_Rust_Examples/Tutorial.thy`,
`Micro_Rust_Examples/Crush_Examples.thy`, and for loops `Tests/Loop_Control/Loop_Control_Automation.thy`.

## Proof shape

- Prove a contract with `crush_boot f: <function>_def contract: <contract>_def`, then `crush_base`.
  This automation is the first step for every program-logic goal (`⊨⇩F`, `𝒲𝒫`, entailments between
  assertions); use the general methods only for the pure goals it leaves.
- Prove the contract of each function before the functions that call it, and pass it to the caller's
  proof with `crush_base specs add: <spec> contracts add: <contract>`. Unfold small helper functions
  with `inline: <definition>`.
- Prove pure facts the automation needs as separate lemmas and pass them with
  `crush_base simp add: <facts>`.
- A call of `crush_boot` or `crush_base` may take up to 60 seconds; test it with
  `isabelle_multi_attempt` and `timeout` 60.

## Loops

- Apply `ucincl_discharge‹rule_tac INV=… and INV'=… and BRK=… and τ=… and θ=… in
  wp_bounded_while_framedI›`, then `crush_base`, as in `Loop_Control_Automation.thy`.
- Write `INV j` for the state with `j` iterations of fuel left. If the body calls functions, include
  `can_alloc_reference` in `INV` and `INV'`.
- `τ` (a `return` in the body) must account for the points-to of the function's local references:
  keep them, or absorb them with `⋆ ⊤`.
- For loop indices, use `unat_loop_index_simps` and `unat_less_of_le_neq_of_nat` (which derives
  `unat i < n` from `unat i ≤ n` and `i ≠ of_nat n`).

## Specifications

- A goal the automation leaves that does not hold, such as a points-to entailing `emp`, means that an
  invariant, `τ`, `θ` or a contract misses a resource or a fact: fix that assertion, not the proof
  method.
- Before adding a precondition about fuel, lengths or arithmetic, read the definitions it concerns
  (`bounded_while`, fuel-bounded recursion, `len`, the arithmetic operations, the contract's abort
  condition) and justify the precondition from them.
