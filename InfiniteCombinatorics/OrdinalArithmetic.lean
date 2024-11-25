import Mathlib

noncomputable section

universe u v w

namespace Ordinal

open Set Order

-- #16996, named iSup_le_iff
protected theorem iSup_le_iff' {ι} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  ciSup_le_iff' (bddAbove_of_small _)

-- #16996, named lt_iSup
protected theorem lt_iSup' {ι} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    a < iSup f ↔ ∃ i, a < f i := by
  rw [← not_iff_not]
  simpa using Ordinal.iSup_le_iff'

-- #16996, named le_iSup
protected theorem le_iSup' {ι} (f : ι → Ordinal.{u}) [Small.{u} ι] : ∀ i, f i ≤ iSup f :=
  le_ciSup (bddAbove_of_small _)

/-- The order isomorphism between ℕ and the first ω ordinals. -/
@[simps! apply]
def relIso_nat_omega0 : ℕ ≃o Iio ω where
  toFun n := ⟨n, nat_lt_omega0 n⟩
  invFun n := Classical.choose (lt_omega0.1 n.2)
  left_inv n := by
    have h : ∃ m : ℕ, n = (m : Ordinal) := ⟨n, rfl⟩
    exact (Nat.cast_inj.1 (Classical.choose_spec h)).symm
  right_inv n := Subtype.eq (Classical.choose_spec (lt_omega0.1 n.2)).symm
  map_rel_iff' := by simp

@[simp]
theorem relIso_nat_omega0_coe_symm_apply (o : Iio ω) : relIso_nat_omega0.symm o = o.1 := by
  obtain ⟨o, h⟩ := o
  rcases lt_omega0.mp h with ⟨n, hn⟩
  simp_rw [hn]
  exact congrArg Nat.cast <| relIso_nat_omega0.symm_apply_apply n

theorem strictMono_of_succ_lt_omega0 {α : Type*} [Preorder α] (f : Iio ω → α)
    (hf : ∀ i, f i < f ⟨succ i, isLimit_omega0.succ_lt i.2⟩) : StrictMono f := by
  have mono := strictMono_nat_of_lt_succ fun n ↦ hf ⟨n, nat_lt_omega0 n⟩
  convert mono.comp relIso_nat_omega0.symm.strictMono
  ext
  simp

-- #14060
/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_sSup {s : Set Ordinal} (hs : BddAbove s) :
    lift.{u} (sSup s) = sSup (lift.{u} '' s) := by
  apply ((le_csSup_iff' (bddAbove_image.{_,u} hs _)).2 fun c hc => _).antisymm (csSup_le' _)
  · intro c hc
    by_contra h
    obtain ⟨d, rfl⟩ := Ordinal.mem_range_lift_of_le (not_le.1 h).le
    simp_rw [lift_le] at h hc
    rw [csSup_le_iff' hs] at h
    exact h fun a ha => lift_le.1 <| hc (mem_image_of_mem _ ha)
  · rintro i ⟨j, hj, rfl⟩
    exact lift_le.2 (le_csSup hs hj)

/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_iSup {ι : Type v} {f : ι → Ordinal.{w}} (hf : BddAbove (range f)) :
    lift.{u} (iSup f) = ⨆ i, lift.{u} (f i) := by
  rw [iSup, iSup, lift_sSup hf, ← range_comp]
  simp [Function.comp_def]
