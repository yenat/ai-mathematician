import Bridge
namespace Megalodon
theorem quotient_remainder_int_nat : (forall x1 : set, (((In x1) ((setminus omega) (Sing Empty))) -> (forall x2 : set, (((In x2) omega) -> ((ex set) (fun x3 : set => ((and ((In x3) int)) ((ex set) (fun x4 : set => ((and ((In x4) x1)) (((eq set) x2) ((add_SNo ((mul_SNo x3) x1)) x4)))))))))))) := by
  intro x1
  intro h2
  intro x3
  intro h4
  have f13 := @Megalodon.«omega_nat_p» _ h4
  have f29 := @Megalodon.«quotient_remainder_nat» _ h2 _ f13
  (apply f29; try clear f29)
  intro x33
  intro h34
  (apply h34; try clear h34)
  intro h35
  intro h36
  (apply h36; try clear h36)
  intro x37
  intro h38
  (apply h38; try clear h38)
  intro h39
  intro h40
  have f54 := @Megalodon.«omega_nat_p» _ h35
  have f77 := @Megalodon.«nat_p_ordinal» _ f54
  have f103 := @Megalodon.«nat_p_ordinal» _ f13
  have f136 := @Megalodon.«setminusE» _ _ _ h2
  (apply f136; try clear f136)
  intro h141
  intro h142
  have f161 := @Megalodon.«omega_nat_p» _ h141
  have f195 := @Megalodon.«nat_p_ordinal» _ f161
  have f249 := @Megalodon.«setminusE» _ _ _ h2
  have f280 := @Megalodon.«nat_p_trans» _ f161 _ h39
  have f325 := @Megalodon.«nat_p_omega» _ f280
  have f381 := @Megalodon.«nat_p_ordinal» _ f280
  have f442 := @Megalodon.«ordinal_In_Or_Subq» _ _ f381 f381
  have f474 := @Megalodon.«mul_nat_p» _ f280 _ f280
  have f519 := @Megalodon.«nat_p_omega» _ f474
  have f556 := @Megalodon.«nat_p_ordinal» _ f474
  (intro q601 hq601; apply hq601 x33)
  apply Megalodon.«andI»
  apply Megalodon.«Subq_omega_int»
  apply h35
  (intro q725 hq725; apply hq725 x37)
  apply Megalodon.«andI»
  apply h39
  (have e790 := @Megalodon.«add_nat_add_SNo»; simp only [b_eq] at e790; rw [e790] at h40)
  (have e821 := @Megalodon.«mul_nat_mul_SNo»; simp only [b_eq] at e821; rw [e821] at h40)
  apply h40
  apply h35
  apply h141
  apply Megalodon.«nat_p_omega»
  apply Megalodon.«mul_nat_p»
  apply f54
  apply f161
  apply f325
end Megalodon
#print axioms Megalodon.quotient_remainder_int_nat
