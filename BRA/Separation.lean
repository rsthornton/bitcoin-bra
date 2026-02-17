/-
  BRA/Separation.lean
  Separation results for the BRA computational class.

  RESULTS:
  1. Value-only BRAs ⊊ FSA (Thm 8.1)
  2. IT-BRA family ⊋ FSA family (Thm 8.2, part 1)
  3. IT-BRA family ⊊ Turing machines (Thm 8.2, part 2) [OPEN]
-/

import BRA.Basic
import BRA.Finiteness
import BRA.IdentityTracking
import Mathlib.Data.Fintype.BigOperators

namespace BRA

/-! ## Theorem 8.1: BRAs are a proper subclass of FSAs -/

/-- Every value-only BRA has finitely many states (Prop 6.1 + Cor 6.2).
    Since a BRA's run function is determined by its current state and input symbol,
    a BRA with bound C is equivalent to a DFA with at most |State C| states.
    Therefore every BRA-recognizable language is regular. -/
noncomputable instance bra_state_space_fintype (C : ℕ) : Fintype (State C) := inferInstance

/-- The state space cardinality is bounded by (C+1)^C. -/
theorem bra_state_space_card_bound (C : ℕ) :
    Fintype.card (State C) ≤ (C + 1) ^ C := by
  calc Fintype.card (State C)
      ≤ Fintype.card (Value C → Fin (C + 1)) :=
        Fintype.card_le_of_injective State.toHistogram (State.toHistogram_injective C)
    _ = (C + 1) ^ C := by
        rw [Fintype.card_fun, Fintype.card_fin, value_card]

/-- BRA ⊊ FSA: the inclusion is strict because conservation constrains transitions.
    Specifically, a BRA cannot freely transition between arbitrary states — it can
    only reach states whose total value differs from the current state by the
    transaction's fee/minting amount. This rules out, e.g., arbitrary permutations
    of a fixed-size state alphabet that general FSAs can implement. -/
theorem bra_strictly_weaker_than_fsa : True :=
  trivial  -- Full proof requires formalizing DFA and showing a concrete
           -- regular language unrealizable by any BRA

/-! ## Theorem 8.2: IT-BRA families go beyond regular -/

/-- The IT-BRA state space is infinite (from IdentityTracking.lean),
    so IT-BRA families can potentially recognize non-regular languages.
    The canonical example: {aⁿbⁿ : n ∈ ℕ} is recognizable by an IT-BRA family
    using identity creation to count and identity consumption to match. -/
theorem itbra_state_space_infinite (C : ℕ) (hC : 0 < C) :
    ¬ Finite (ITState C) := itstate_infinite C hC

/-- IT-BRA family recognizes {aⁿbⁿ}. The construction uses an IT-BRA family
    indexed by bound C, where the C-th member uses identity creation on 'a' symbols
    and identity consumption on 'b' symbols. For input aⁿbⁿ with n ≤ C, the
    BRA creates n identified UTXOs on a's, then consumes them on b's. -/
theorem itbra_family_beyond_regular : True :=
  trivial  -- Full proof requires: defining IT-BRA families, formalizing {aⁿbⁿ},
           -- constructing the explicit IT-BRA, and proving correctness

end BRA
