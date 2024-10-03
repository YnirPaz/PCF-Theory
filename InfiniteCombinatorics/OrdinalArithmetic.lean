import Mathlib

noncomputable section

universe u

namespace Ordinal

open Set Order

-- #16663

@[elab_as_elim]
def boundedLimitRecOn {l : Ordinal} (lLim : l.IsLimit) {C : Iio l → Sort*} (o : Iio l)
    (H₁ : C ⟨0, lLim.pos⟩) (H₂ : (o : Iio l) → C o → C ⟨succ o, lLim.succ_lt o.2⟩)
    (H₃ : (o : Iio l) → IsLimit o → (Π o' < o, C o') → C o) : C o :=
  limitRecOn (C := fun p ↦ (h : p < l) → C ⟨p, h⟩) o.1 (fun _ ↦ H₁)
    (fun o ih h ↦ H₂ ⟨o, _⟩ <| ih <| (lt_succ o).trans h)
    (fun _o ho ih _ ↦ H₃ _ ho fun _o' h ↦ ih _ h _) o.2

@[simp]
theorem boundedLimitRec_zero {l} (lLim : l.IsLimit) {C} (H₁ H₂ H₃) :
    @boundedLimitRecOn l lLim C ⟨0, lLim.pos⟩ H₁ H₂ H₃ = H₁ := by
  rw [boundedLimitRecOn, limitRecOn_zero]

@[simp]
theorem boundedLimitRec_succ {l} (lLim : l.IsLimit) {C} (o H₁ H₂ H₃) :
    @boundedLimitRecOn l lLim C ⟨succ o.1, lLim.succ_lt o.2⟩ H₁ H₂ H₃ = H₂ o
    (@boundedLimitRecOn l lLim C o H₁ H₂ H₃) := by
  rw [boundedLimitRecOn, limitRecOn_succ]
  rfl

theorem boundedLimitRec_limit {l} (lLim : l.IsLimit) {C} (o H₁ H₂ H₃ oLim) :
    @boundedLimitRecOn l lLim C o H₁ H₂ H₃ = H₃ o oLim (fun x _ ↦
    @boundedLimitRecOn l lLim C x H₁ H₂ H₃) := by
  rw [boundedLimitRecOn, limitRecOn_limit]
  rfl


-- #16710
theorem isLimit_of_not_succ_of_ne_zero {o : Ordinal} (h : ¬∃ a, o = succ a) (h' : o ≠ 0) :
  IsLimit o := ((zero_or_succ_or_limit o).resolve_left h').resolve_left h

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


/-- The natural isomorphism between ℕ and the first ω ordinals. -/
def relIso_nat_omega : ℕ ≃o Iio ω where
  toFun n := ⟨n, nat_lt_omega n⟩
  invFun n := Classical.choose (lt_omega.1 n.2)
  left_inv n := by
    have h : ∃ m : ℕ, n = (m : Ordinal) := ⟨n, rfl⟩
    exact (Ordinal.natCast_inj.1 (Classical.choose_spec h)).symm
  right_inv n := Subtype.eq (Classical.choose_spec (lt_omega.1 n.2)).symm
  map_rel_iff' := @natCast_le

theorem relIso_nat_omega.symm_eq {o : Ordinal} (h : o < ω) :
    relIso_nat_omega.symm ⟨o, h⟩ = o := by
  rcases lt_omega.mp h with ⟨n, rfl⟩
  exact congrArg Nat.cast <| relIso_nat_omega.symm_apply_apply n

theorem strictMono_of_succ_lt_omega {o : Ordinal} (f : Iio ω → Iio o)
    (hf : ∀ i, f i < f ⟨succ i, omega_isLimit.succ_lt i.2⟩) (i j) (h : i < j) : f i < f j := by
  have mono := strictMono_nat_of_lt_succ fun n ↦ hf ⟨n, nat_lt_omega n⟩
  have := mono <| (OrderIso.lt_iff_lt relIso_nat_omega.symm).mpr h
  change f ⟨relIso_nat_omega.symm ⟨i.1, i.2⟩, _⟩ <
    f ⟨relIso_nat_omega.symm ⟨j.1, j.2⟩, _⟩ at this
  simp_rw [relIso_nat_omega.symm_eq] at this
  exact this
