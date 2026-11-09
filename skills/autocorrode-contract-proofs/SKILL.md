---
name: autocorrode-contract-proofs
description: Rules for proving contracts of uRust functions in AutoCorrode (crush_boot and crush_base, loops, specifications). Use together with isabelle-proof-development whenever you prove an AutoCorrode function contract.
---

# Proving AutoCorrode contracts

Follow the worked examples: `Micro_Rust_Examples/Showcase.thy`, `Tutorial.thy`, `Crush_Examples.thy`,
and for loops `Tests/Loop_Control/Loop_Control_Automation.thy`.

## Proofs

- Start every contract proof with `crush_boot f: <function>_def contract: <contract>_def`, then
  `crush_base`; use general methods only for the pure goals it leaves.
- Prove a callee's contract before its callers and pass it with
  `crush_base specs add: <spec> contracts add: <contract>`; unfold small helpers with
  `inline: <definition>`.
- Give `crush_base` the pure facts it needs with `simp add:`.
- A `crush_boot` or `crush_base` step may take up to 60 seconds: test it with
  `isabelle_multi_attempt` and `timeout` 60.

## Loops

- Use `ucincl_discharge‹rule_tac INV=… and INV'=… and BRK=… and τ=… and θ=… in
  wp_bounded_while_framedI›`, then `crush_base`.
- `INV j` is the state with `j` iterations of fuel left. If the body calls a function whose contract
  needs `can_alloc_reference`, include it in `INV` and `INV'`.
- `τ` (a `return` in the body) must keep the points-to of the function's local references, or absorb
  them with `⋆ ⊤`.
- `unat_plus_one_of_less_bound` gives `unat (i + 1) = Suc (unat i)` from `unat i < n` and
  `n < 2^LENGTH('a)`.

## Specifications

- If `crush_base` leaves a goal that does not hold, such as a points-to entailing `emp`, fix the
  invariant, `τ`, `θ` or contract that misses the resource or fact, not the proof method.
- Before adding a precondition about fuel, lengths or arithmetic, read the definitions it concerns
  (`bounded_while`, `len`, the arithmetic operations, the contract's abort condition) and justify it
  from them.
