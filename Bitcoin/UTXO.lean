/-
  Bitcoin/UTXO.lean
  Bitcoin's UTXO model as a symmetric monoidal category,
  following Nester (2020) with extensions for fees.
-/

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace Bitcoin

/-! ## The base resource theory: N_ν^δ -/

/-- A coin value (positive natural number). -/
abbrev CoinValue := ℕ

/-- A Bitcoin address (owner identifier).
    We use ℕ for concreteness rather than an axiom. -/
abbrev Addr := ℕ

/-- An owned UTXO: a value associated with an address. -/
structure OwnedUTXO where
  value : ℕ
  owner : Addr
  value_pos : 0 < value
deriving DecidableEq

/-- A UTXO set: the state of Bitcoin's ledger at a point in time. -/
abbrev UTXOSet := Multiset OwnedUTXO

/-- Total value of a UTXO set -/
def UTXOSet.totalValue (s : UTXOSet) : ℕ :=
  (s.map (·.value)).sum

/-! ## Transaction morphisms -/

/-- A Bitcoin transaction (morphism in the UTXO category). -/
structure Transaction where
  /-- UTXOs consumed (inputs) -/
  inputs : Multiset OwnedUTXO
  /-- UTXOs produced (outputs) -/
  outputs : Multiset OwnedUTXO
  /-- Minted value (coinbase reward, 0 for normal transactions) -/
  coinbase : ℕ
  /-- Conservation: inputs + coinbase ≥ outputs -/
  conservation :
    (inputs.map (·.value)).sum + coinbase ≥ (outputs.map (·.value)).sum

/-- Transaction fee -/
def Transaction.fee (tx : Transaction) : ℕ :=
  (tx.inputs.map (·.value)).sum + tx.coinbase - (tx.outputs.map (·.value)).sum

/-- Apply a transaction to a UTXO set -/
def UTXOSet.applyTx (s : UTXOSet) (tx : Transaction) : Option UTXOSet :=
  if tx.inputs ≤ s then
    some (s - tx.inputs + tx.outputs)
  else
    none

/-! ## The conservation functor -/

/-- Conservation: total value is preserved modulo fees and coinbase.
    Additive form avoids ℕ truncated subtraction issues. -/
theorem conservation_functor (s : UTXOSet) (tx : Transaction)
    (h : tx.inputs ≤ s) :
    (s - tx.inputs + tx.outputs).totalValue + tx.fee =
      s.totalValue + tx.coinbase := by
  -- totalValue is additive over multiset addition
  have htv_add : ∀ (a b : UTXOSet),
      UTXOSet.totalValue (a + b) = UTXOSet.totalValue a + UTXOSet.totalValue b := by
    intro a b; simp [UTXOSet.totalValue, Multiset.map_add, Multiset.sum_add]
  -- Decompose LHS: totalValue(remainder + outputs) = totalValue(remainder) + totalValue(outputs)
  rw [htv_add]
  -- Decompose s.totalValue using s = (s - inputs) + inputs
  have hS : UTXOSet.totalValue s =
      UTXOSet.totalValue (s - tx.inputs) + UTXOSet.totalValue tx.inputs := by
    conv_lhs => rw [← Multiset.sub_add_cancel h]
    exact htv_add (s - tx.inputs) tx.inputs
  rw [hS]
  -- Now pure ℕ: R + O + fee = R + I + c, where fee = I + c - O and O ≤ I + c
  simp only [Transaction.fee, UTXOSet.totalValue]
  have := tx.conservation
  omega

/-! ## Morphism classification for security analysis -/

/-- Classification of transaction morphisms by their computational nature. -/
inductive MorphismClass
  | mint      -- coinbase, secured by SHA-256
  | transfer  -- ownership change, secured by ECDSA
  | split     -- value restructuring, pure arithmetic
  | merge     -- value restructuring, pure arithmetic
  | dissipate -- fee payment, irreversible

/-- Quantum vulnerability by morphism class -/
def MorphismClass.quantumVulnerable : MorphismClass → Prop
  | .mint => False       -- Grover: quadratic speedup only
  | .transfer => True    -- Shor: polynomial-time key recovery
  | .split => False      -- Pure arithmetic
  | .merge => False      -- Pure arithmetic
  | .dissipate => False  -- Irreversible

end Bitcoin
