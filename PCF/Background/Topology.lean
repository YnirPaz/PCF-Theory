import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Topology.DerivedSet
import PCF.Background.Ordinal

open Classical
open Set Order Cardinal

universe u v

namespace Ordinal

-- Small.{u} → Small.{max u v} isn't properly synthed, so this instance is required.
instance {o : Ordinal.{u}} : Small.{max u v} (Iio o) := small_lift (Iio o)

instance instNoMaxOrderIio {o : Ordinal} {h : o.IsLimit} : NoMaxOrder (Iio o) :=
  ⟨by
    intro a
    use succ a
    rw [← Subtype.coe_lt_coe, coe_succ_Iio h.isSuccPrelimit]
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

theorem mk_derivedSet_le (S : Set Ordinal) : #(derivedSet S) ≤ #S := by
  by_cases hS : S.Finite
  · exact mk_le_mk_of_subset <| (isClosed_iff_derivedSet_subset _).mp hS.isClosed
  /- `f` sends each accumulation point of `S` to the smallest element of `S` above it,
  if it exists. This is an injection from the accumulation points to `Option S`. -/
  let f : derivedSet S → Option S := fun δ ↦ if h : (S ∩ Ioi δ).Nonempty then
    some ⟨sInf (S ∩ Ioi δ.1), inter_subset_left (csInf_mem h)⟩
    else none
  suffices hf : Function.Injective f by
    convert mk_le_of_injective hf using 1
    rw [mk_option]
    refine (add_one_of_aleph0_le ?_).symm
    exact infinite_iff.mp (infinite_coe_iff.mpr hS)
  intro a b hab
  by_cases hemp : ¬(S ∩ Ioi a.1).Nonempty ∨ ¬(S ∩ Ioi b.1).Nonempty
  · wlog ha : ¬(S ∩ Ioi a.1).Nonempty
    · have aux : ¬(S ∩ Ioi b.1).Nonempty := by tauto
      exact (this S hS hab.symm (Or.inl aux) aux).symm
    unfold f at hab
    rw [dif_neg ha] at hab
    split_ifs at hab with hb
    refine ((lt_trichotomy a b).resolve_left ?_).resolve_right ?_
    · intro altb
      obtain ⟨x, hx⟩ := IsAcc.forall_lt b.2 a altb
      exact ha ⟨x, ⟨hx.1, hx.2.1⟩⟩
    · intro blta
      obtain ⟨x, hx⟩ := IsAcc.forall_lt a.2 b blta
      exact hb ⟨x, ⟨hx.1, hx.2.1⟩⟩
  push_neg at hemp
  unfold f at hab
  rw [dif_pos hemp.1, dif_pos hemp.2, Option.some_inj] at hab
  by_contra! h
  --sorry -- wlog bug which should be fixed soon. see https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/WLOG.20bug.3F

  wlog altb : a < b
  · exact this S hS (And.comm.mp hemp) hab.symm h.symm
      ((not_lt_iff_eq_or_lt.mp altb).resolve_left h)
  have blt : b ≤ sInf (S ∩ Ioi b) := le_csInf hemp.2 fun _ ⟨_, h⟩ ↦ h.le
  have ltb : sInf (S ∩ Ioi a) < b := by
    obtain ⟨x, hx⟩ := IsAcc.forall_lt b.2 a altb
    exact csInf_lt_of_lt (a := x) (OrderBot.bddBelow _) ⟨hx.1, hx.2.1⟩ hx.2.2
  have : sInf (S ∩ Ioi a) = sInf (S ∩ Ioi b) :=
    congrArg Subtype.val hab
  rw [← this] at blt
  exact blt.not_lt ltb


theorem isClosedBelow_derivedSet {S : Set Ordinal} :
    ∀ o, IsClosedBelow (S ∪ (derivedSet S)) o := fun o ↦ by
  rw [isClosedBelow_iff]
  intro p plto pacc
  right
  apply (isAcc_iff _ _).mpr
  refine ⟨(IsAcc.pos pacc).ne.symm, ?_⟩
  intro q qltp
  obtain ⟨x, hx⟩ := IsAcc.forall_lt pacc q qltp
  cases' hx.1 with xs xds
  · exact ⟨x, ⟨xs, hx.2⟩⟩
  obtain ⟨y, hy⟩ := IsAcc.forall_lt xds q hx.2.1
  exact ⟨y, ⟨hy.1, ⟨hy.2.1, hy.2.2.trans hx.2.2⟩⟩⟩

end Ordinal
