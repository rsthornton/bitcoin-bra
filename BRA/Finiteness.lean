/-
  BRA/Finiteness.lean
  Proof that the state space of a value-only BRA is finite.

  PROOF STRATEGY:
  1. Show Value C ≃ Fin C, hence Fintype
  2. Show multiset card ≤ sum when all elements ≥ 1
  3. Use histogram injection: State C ↪ (Value C → Fin (C+1))
  4. Conclude Fintype (State C)
-/

import BRA.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Multiset.Count

namespace BRA

/-! ## Step 1: Value C is finite -/

/-- Value C = {v : ℕ // 0 < v ∧ v ≤ C} is equivalent to Fin C via v ↦ v - 1. -/
def Value.equivFin (C : ℕ) : Value C ≃ Fin C where
  toFun v := ⟨v.val - 1, by have := v.property; omega⟩
  invFun i := ⟨i.val + 1, by have := i.isLt; omega⟩
  left_inv v := by
    apply Subtype.ext
    simp only
    have := v.property
    omega
  right_inv i := by
    apply Fin.ext
    simp only
    omega

instance (C : ℕ) : Fintype (Value C) :=
  Fintype.ofEquiv (Fin C) (Value.equivFin C).symm

/-- The cardinality of Value C is C. -/
theorem value_card (C : ℕ) : Fintype.card (Value C) = C := by
  rw [Fintype.card_congr (Value.equivFin C), Fintype.card_fin]

/-! ## Step 2: Bounded multisets are finite -/

/-- If every element of a multiset of naturals is ≥ 1, then card ≤ sum. -/
private lemma card_le_sum_of_one_le (s : Multiset ℕ) (h : ∀ x ∈ s, 1 ≤ x) :
    s.card ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, Multiset.sum_cons]
    have ha : 1 ≤ a := h a (Multiset.mem_cons_self a s)
    have hs : s.card ≤ s.sum := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    omega

/-- The number of elements in any state is at most C. -/
theorem state_size_bound {C : ℕ} (s : State C) : s.size ≤ C := by
  unfold State.size
  calc s.utxos.card
      = (s.utxos.map (·.val)).card := (Multiset.card_map _ _).symm
    _ ≤ (s.utxos.map (·.val)).sum := by
        apply card_le_sum_of_one_le
        intro x hx
        rw [Multiset.mem_map] at hx
        obtain ⟨v, _, rfl⟩ := hx
        exact v.property.1
    _ ≤ C := s.bound

/-! ## Step 3: State C is finite (via histogram injection) -/

/-- Histogram: for each possible value, how many UTXOs have that value.
    Each count is ≤ card ≤ C, so fits in Fin (C + 1). -/
def State.toHistogram {C : ℕ} (s : State C) : Value C → Fin (C + 1) :=
  fun v => ⟨s.utxos.count v, by
    have h1 : s.utxos.count v ≤ Multiset.card s.utxos := Multiset.count_le_card v s.utxos
    have h2 : s.utxos.card ≤ C := state_size_bound s
    omega⟩

/-- Two states with the same histogram are equal. -/
theorem State.toHistogram_injective (C : ℕ) :
    Function.Injective (State.toHistogram (C := C)) := by
  intro ⟨u₁, b₁⟩ ⟨u₂, b₂⟩ h
  have hutxos : u₁ = u₂ := by
    ext a
    have ha := congr_fun h a
    exact Fin.val_eq_of_eq ha
  cases hutxos
  rfl

/-- The state space of a BRA with bound C is a finite type. -/
noncomputable instance (C : ℕ) : Fintype (State C) :=
  Fintype.ofInjective State.toHistogram (State.toHistogram_injective C)

/-! ## Main finiteness result -/

/-- PROPOSITION 6.1: The state space of any BRA with bound C is finite. -/
theorem state_space_finite (C : ℕ) : Finite (State C) := inferInstance

end BRA
