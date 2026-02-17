/-
  BRA/Basic.lean
  Core definitions for Bounded-Resource Automata

  This file defines:
  - The value domain 𝕊 = {1, ..., C}
  - BRA states as multisets over 𝕊 with bounded total value
  - The BRA transition function with conservation constraint
  - Bitcoin as a BRA instance

  WORKFLOW NOTE: Start here. Get these definitions to compile before
  attempting any theorems. The definitions encode the key design decisions
  and getting them right is 80% of the work.
-/

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Fold
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs

namespace BRA

/-! ## Value Domain -/

/-- A value is a positive natural number at most C.
    Represents a single UTXO's satoshi value. -/
def Value (C : ℕ) := {v : ℕ // 0 < v ∧ v ≤ C}

instance (C : ℕ) : DecidableEq (Value C) :=
  inferInstanceAs (DecidableEq {v : ℕ // 0 < v ∧ v ≤ C})

/-- Extract the numeric value -/
def Value.IsVal {C : ℕ} (v : Value C) : ℕ := v.val

/-! ## Helper: sum of values in a multiset -/

/-- Total numeric value of a multiset of Values -/
def sumValues {C : ℕ} (s : Multiset (Value C)) : ℕ :=
  (s.map (·.val)).sum

/-! ## States -/

/-- A BRA state is a finite multiset of values whose total does not exceed C.
    Represents the UTXO set abstracted to values only (no identity tracking). -/
structure State (C : ℕ) where
  /-- The multiset of active values -/
  utxos : Multiset (Value C)
  /-- Total value is bounded -/
  bound : sumValues utxos ≤ C

/-- Total value of a state -/
def State.totalValue {C : ℕ} (s : State C) : ℕ :=
  sumValues s.utxos

/-- The empty state (genesis before any minting) -/
def State.empty (C : ℕ) : State C where
  utxos := ∅
  bound := by
    simp [sumValues, Multiset.map_zero, Multiset.sum_zero]

/-- Number of UTXOs in a state -/
def State.size {C : ℕ} (s : State C) : ℕ := s.utxos.card

/-! ## Transitions -/

/-- A transition specification: what to consume and what to produce.
    Conservation requires: total consumed + minted ≥ total produced.
    The difference is the fee. -/
structure TransitionSpec (C : ℕ) where
  /-- Values of UTXOs consumed (must be subset of current state) -/
  consumed : Multiset (Value C)
  /-- Values of UTXOs produced -/
  produced : Multiset (Value C)
  /-- Value minted (coinbase). Zero for non-coinbase transactions. -/
  minted : ℕ
  /-- Conservation: consumed + minted ≥ produced -/
  conservation : sumValues consumed + minted ≥ sumValues produced

/-- The fee of a transition -/
def TransitionSpec.fee {C : ℕ} (t : TransitionSpec C) : ℕ :=
  sumValues t.consumed + t.minted - sumValues t.produced

/-- Apply a transition to a state, if valid.
    Returns none if consumed UTXOs aren't available in current state,
    or if the resulting state would exceed the bound. -/
def State.apply {C : ℕ} (s : State C) (t : TransitionSpec C) : Option (State C) :=
  -- Check that consumed is a sub-multiset of current UTXOs
  if t.consumed ≤ s.utxos then
    let remaining := s.utxos - t.consumed
    let new_utxos := remaining + t.produced
    -- Check that new total doesn't exceed bound
    if h_bound : sumValues new_utxos ≤ C then
      some ⟨new_utxos, h_bound⟩
    else
      none
  else
    none

/-! ## The BRA as a computational model -/

/-- A Bounded-Resource Automaton over an input alphabet. -/
structure BoundedResourceAutomaton (α : Type) where
  /-- Resource bound -/
  resourceBound : ℕ
  /-- Initial state -/
  init : State resourceBound
  /-- Transition function: given current state and input symbol,
      produce a transition specification (or reject) -/
  step : State resourceBound → α → Option (TransitionSpec resourceBound)
  /-- Accepting states -/
  accept : State resourceBound → Prop

/-- Run a BRA on an input string, returning the final state if all
    transitions are valid. -/
def BoundedResourceAutomaton.run {α : Type}
    (bra : BoundedResourceAutomaton α) : List α → Option (State bra.resourceBound)
  | [] => some bra.init
  | (a :: as) => do
    let s ← bra.run as
    let spec ← bra.step s a
    s.apply spec

/-! ## Key observations (to be proved in Finiteness.lean)

  1. For fixed C, the number of distinct State C values is finite.
     This is because each state is a multiset over {1,...,C} with
     sum ≤ C, and the number of such multisets equals the number
     of integer partitions of n into parts from {1,...,C}, summed
     over n from 0 to C.

  2. Therefore, every value-only BRA is a finite-state machine.
     But NOT every FSA is a BRA — the conservation constraint
     restricts available transitions.
-/

end BRA
