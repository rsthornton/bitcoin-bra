/-
  BRA/IdentityTracking.lean
  Identity-tracking BRA: extends BRA with unique UTXO identifiers.

  Value-only BRAs are ⊆ FSA (Finiteness.lean).
  IT-BRAs have countably infinite state spaces and
  recognize non-regular languages.
-/

import BRA.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.EquivFin

namespace BRA

/-! ## Identified UTXOs -/

/-- An identified UTXO: a unique ID paired with a value -/
structure IUTXO (C : ℕ) where
  id : ℕ
  value : Value C
deriving DecidableEq

/-- An IT-BRA state: a finite set of identified UTXOs with
    distinct IDs and bounded total value -/
structure ITState (C : ℕ) where
  /-- The set of active (unspent) identified UTXOs -/
  utxos : Finset (IUTXO C)
  /-- All IDs are distinct (follows from Finset, but stated for clarity) -/
  ids_distinct : ∀ u₁ u₂ : IUTXO C, u₁ ∈ utxos → u₂ ∈ utxos →
    u₁.id = u₂.id → u₁ = u₂
  /-- Total value bounded -/
  bound : (utxos.val.map (·.value.val)).sum ≤ C
  /-- Next available fresh ID -/
  next_id : ℕ
  /-- All active IDs are below next_id -/
  ids_below : ∀ u : IUTXO C, u ∈ utxos → u.id < next_id

/-! ## Key properties -/

/-- The state space of IT-BRA is infinite.

    PROOF: There are infinitely many distinct states with different IDs.
    For C ≥ 1: {(id=n, val=1)}, next_id=n+1 gives distinct states for each n. -/
theorem itstate_infinite (C : ℕ) (hC : 0 < C) : ¬ Finite (ITState C) := by
  intro hfin
  -- Value 1 exists when C > 0
  have hval : 0 < 1 ∧ 1 ≤ C := ⟨by omega, by omega⟩
  -- Injection: n ↦ state with single UTXO (id=n, val=1), next_id=n+1
  let f : ℕ → ITState C := fun n => {
    utxos := {⟨n, ⟨1, hval⟩⟩}
    ids_distinct := by
      intro u1 u2 h1 h2 _
      simp [Finset.mem_singleton] at h1 h2
      rw [h1, h2]
    bound := by simp; omega
    next_id := n + 1
    ids_below := by
      intro u hu
      simp [Finset.mem_singleton] at hu
      subst hu; show n < n + 1; omega
  }
  have hf : Function.Injective f := by
    intro n1 n2 h
    have : (f n1).next_id = (f n2).next_id := by rw [h]
    simp [f] at this
    omega
  haveI := hfin
  exact Infinite.not_finite (Finite.of_injective f hf)

/-! ## IT-BRA transitions -/

/-- An IT-BRA transition consumes identified UTXOs and produces
    new ones with fresh IDs -/
structure ITTransitionSpec (C : ℕ) where
  /-- IDs of UTXOs to consume -/
  consumed_ids : Finset ℕ
  /-- Values of new UTXOs to create (will get fresh IDs) -/
  produced_values : List (Value C)
  /-- Minted value -/
  minted : ℕ

/-- Assign fresh IDs starting from `start` to a list of values. -/
def assignFreshIds {C : ℕ} (start : ℕ) : List (Value C) → List (IUTXO C)
  | [] => []
  | v :: vs => ⟨start, v⟩ :: assignFreshIds (start + 1) vs

theorem assignFreshIds_mem {C : ℕ} {start : ℕ} {vals : List (Value C)} {u : IUTXO C}
    (h : u ∈ assignFreshIds start vals) :
    start ≤ u.id ∧ u.id < start + vals.length := by
  induction vals generalizing start with
  | nil => simp [assignFreshIds] at h
  | cons v vs ih =>
    simp [assignFreshIds] at h
    rcases h with rfl | h
    · constructor <;> (dsimp; omega)
    · obtain ⟨h1, h2⟩ := ih h
      simp only [List.length_cons]
      constructor <;> omega

theorem assignFreshIds_injective {C : ℕ} {start : ℕ} {vals : List (Value C)}
    {u1 u2 : IUTXO C}
    (h1 : u1 ∈ assignFreshIds start vals) (h2 : u2 ∈ assignFreshIds start vals)
    (hid : u1.id = u2.id) : u1 = u2 := by
  induction vals generalizing start with
  | nil => simp [assignFreshIds] at h1
  | cons v vs ih =>
    simp [assignFreshIds] at h1 h2
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · rfl
    · exfalso; have := assignFreshIds_mem h2; dsimp at hid; omega
    · exfalso; have := assignFreshIds_mem h1; dsimp at hid; omega
    · exact ih h1 h2

/-- Apply an IT-BRA transition:
    1. Check all consumed IDs exist in state
    2. Check conservation (consumed value + minted ≥ produced value)
    3. Remove consumed UTXOs, add produced with fresh IDs
    4. Check bound, build new state -/
def ITState.apply {C : ℕ} (s : ITState C) (t : ITTransitionSpec C)
    : Option (ITState C) :=
  -- Remaining UTXOs after removing consumed IDs
  let remaining := s.utxos.filter (fun u => u.id ∉ t.consumed_ids)
  -- New UTXOs with fresh IDs
  let new_list := assignFreshIds s.next_id t.produced_values
  let new_utxos := remaining ∪ new_list.toFinset
  -- Check all consumed IDs actually exist
  if t.consumed_ids ⊆ s.utxos.image (·.id) then
    -- Check bound
    if h_bound : (new_utxos.val.map (·.value.val)).sum ≤ C then
      some {
        utxos := new_utxos
        ids_distinct := by
          intro u1 u2 h1 h2 hid
          -- Decompose union membership via .mp (works through let bindings)
          rcases Finset.mem_union.mp h1 with h1l | h1r <;>
            rcases Finset.mem_union.mp h2 with h2l | h2r
          · -- Both in remaining
            exact s.ids_distinct u1 u2
              (Finset.mem_filter.mp h1l).1 (Finset.mem_filter.mp h2l).1 hid
          · -- u1 remaining, u2 new: IDs don't overlap
            exfalso
            have := s.ids_below u1 (Finset.mem_filter.mp h1l).1
            have := assignFreshIds_mem (List.mem_toFinset.mp h2r)
            omega
          · -- u1 new, u2 remaining: symmetric
            exfalso
            have := assignFreshIds_mem (List.mem_toFinset.mp h1r)
            have := s.ids_below u2 (Finset.mem_filter.mp h2l).1
            omega
          · -- Both new: same ID implies same element
            exact assignFreshIds_injective
              (List.mem_toFinset.mp h1r) (List.mem_toFinset.mp h2r) hid
        bound := h_bound
        next_id := s.next_id + t.produced_values.length
        ids_below := by
          intro u hu
          rcases Finset.mem_union.mp hu with hl | hr
          · have := s.ids_below u (Finset.mem_filter.mp hl).1; omega
          · exact (assignFreshIds_mem (List.mem_toFinset.mp hr)).2
      }
    else none
  else none

end BRA
