import Mathlib
import InfiniteCombinatorics.OrdinalArithmetic
import InfiniteCombinatorics.OrdinalBasic

universe u v

open Set Order

namespace Ordinal

-- Small.{u} → Small.{max u v} isn't properly synthed, so this instance is required.
instance {o : Ordinal.{u}} : Small.{max u v} (Iio o) := small_lift (Iio o)

theorem coe_succ_Iio {o : Ordinal} {h : o.IsLimit} {α : Iio o} : (succ α).1 = α.1 + 1 := by
  rw [Ordinal.add_one_eq_succ]
  apply coe_succ_of_mem
  have := Subtype.mem α
  rw [mem_Iio] at this ⊢
  exact h.succ_lt this

theorem succ_Iio {o : Ordinal} {h : o.IsLimit} {α : Iio o} : succ α = ⟨α.1 + 1, h.succ_lt α.2⟩ :=
  Subtype.val_inj.mp <| coe_succ_Iio (h := h)

instance instNoMaxOrderIio {o : Ordinal} {h : o.IsLimit} : NoMaxOrder (Iio o) :=
  ⟨by
    intro a
    use succ a
    rw [← Subtype.coe_lt_coe, coe_succ_Iio (h := h)]
    exact lt_succ a.1⟩

theorem IsAcc.inter_Ioi {o p : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) (hp : p < o) :
    o.IsAcc (S ∩ Ioi p) := by
  rw [isAcc_iff]
  refine ⟨h.pos.ne.symm, fun q hq ↦ ?_⟩
  obtain ⟨x, xmem⟩ := h.forall_lt (max p q) (max_lt hp hq)
  use x
  exact ⟨⟨xmem.1, (max_lt_iff.mp xmem.2.1).1⟩, ⟨(max_lt_iff.mp xmem.2.1).2, xmem.2.2⟩⟩

theorem isAcc_iSup {o : Ordinal.{u}} {α : Iio o} (ho : o.IsLimit) (f : Iio o → Ordinal.{v})
    [Small.{v} (Iio o)] (hf : ∀ α β, α < β → f α < f β) {S : Set Ordinal} (hp : ∀ β, α < β → f β ∈ S) :
    (iSup f).IsAcc S := by
  have : NoMaxOrder ↑(Iio o) := instNoMaxOrderIio (h := ho)
  have : Nonempty (Iio o) := ⟨⟨0, ho.pos⟩⟩
  rw [isAcc_iff]
  constructor
  · have flt := hf ⟨0, ho.pos⟩ ⟨1, ho.one_lt⟩ (Subtype.mk_lt_mk.mpr zero_lt_one)
    have lesup := le_ciSup (f := f) (bddAbove_of_small _) ⟨1, ho.one_lt⟩
    intro h
    have := h ▸ bot_lt_of_lt (flt.trans_le lesup)
    exact not_lt_bot this
  · intro β hβ
    obtain ⟨γ, hγ⟩ := (lt_ciSup_iff (bddAbove_of_small _)).mp hβ
    use f (succ (max α γ))
    constructor
    · exact hp (succ (max α γ)) <| (le_max_left α γ).trans_lt (lt_succ (max α γ))
    · constructor
      · exact hγ.trans <| hf _ _ <| (le_max_right α γ).trans_lt (lt_succ (max α γ))
      · apply (lt_ciSup_iff (bddAbove_of_small _)).mpr
        use succ (succ (max α γ))
        exact hf _ _ (lt_succ _)

end Ordinal
