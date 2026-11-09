---
name: autocorrode-contract-proofs
description: Rules for proving contracts of uRust functions in AutoCorrode (crush_boot and crush_base, loops, recursion, specifications). Use together with isabelle-proof-development whenever you prove an AutoCorrode function contract.
---

# Proving AutoCorrode contracts

Follow the worked examples: `Micro_Rust_Examples/Showcase.thy`, `Tutorial.thy`, `Crush_Examples.thy`,
and for loops `Tests/Loop_Control/Loop_Control_Automation.thy`.

## Proofs

- Start every contract proof with `crush_boot f: <function>_def contract: <contract>_def`, then
  `crush_base`; use general methods only for the pure goals it leaves.
- Prove a callee's contract before its callers and pass it with
  `crush_base specs add: <spec> contracts add: <contract>`. Unfold small helpers and struct
  constructors (`<Type>_mk_def`) with `inline:`.
- Give `crush_base` the pure facts it needs as `count_skip_spec` does: open the proof with
  `proof (crush_boot …, goal_cases) case 1`, add the facts with `moreover`, and finish with
  `ultimately show ?case` and `crush_base`.
- Hide a case distinction or quantifier that `crush_base` should not split behind a local `define`,
  and add its defining facts.
- A `crush_boot` or `crush_base` step may take up to 60 seconds: test it with
  `isabelle_multi_attempt` and `timeout` 60.

## Loops

- Use `ucincl_discharge‹rule_tac INV=… and INV'=… and BRK=… and τ=… and θ=… in
  wp_bounded_while_framedI›`, then `crush_base`.
- `INV j` is the state with `j` iterations of fuel left. `INV 0` must also hold when the loop exits
  because its condition is false: state the exit facts as `j = 0 ⟶ …` and the fuel facts as
  `0 < j ⟶ …`.
- `τ` (a `return` in the body) must entail the function's postcondition, `can_alloc_reference`
  included, and keep the points-to of the function's local references or absorb them with `⋆ ⊤`.
- `unat_plus_one_of_less_bound` gives `unat (i + 1) = Suc (unat i)` from `unat i < n` and
  `n < 2^LENGTH('a)`.

## Recursion

- A recursive function is `(step ^^ urust_fuel) P`. Give it a contract `C n …` indexed by the fuel
  whose precondition is false at fuel `0`, unfold the function and apply
  `rule satisfies_function_contract_funpow<k>[where 𝒞=C]` (`k` = number of arguments). Prove the
  base case with `crush_boot contract: <C>_def` and `crush_base`, and the step with
  `crush_boot f: <step>_def contract: <C>_def` and `crush_base specs add: <induction hypothesis>`.

## Specifications

- When `bounded_while` runs out of fuel it does nothing (`skip`); a recursion that runs out of fuel
  panics, and a contract's abort postcondition is `⊥`. Require enough fuel for every iteration
  and every recursion level.
- `len xs` is `of_nat (length xs)`, and `+`, `-`, `*` panic on overflow: require the bounds that
  rule this out (such as `length xs < 2^64`). Convert word and nat comparisons with
  `word_less_of_nat_iff` and `word_eq_of_nat_iff`.
- If `crush_base` leaves a goal that does not hold, such as a points-to entailing `emp`, fix the
  invariant, `τ`, `θ` or contract that misses the resource or fact, not the proof method.
