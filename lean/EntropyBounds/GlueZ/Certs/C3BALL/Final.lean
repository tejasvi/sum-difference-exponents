import EntropyBounds.GlueZ.Certs.C3BALL.Rows0
import EntropyBounds.GlueZ.Certs.C3BALL.Rows1

set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Finset

/-!
# The sum-difference certificate `c3b_allgroups.json`, checked in Lean

`entropy_ineq`: `H(X, Y) ≤ 882/1259 H(X) + 1609/2518 H(Y) + 2467/5036 H(X + Y)` for every finitely supported pair of random
variables in every abelian group `G`, with `x − y` injective on the support; `set_ineq`: for finite
`A, B ⊆ G` and `P ⊆ A × B`, `|A −_P B| ≤ max(|A|, |B|, |A +_P B|)^C`, `C = 9213/5036` (Tao's page 3b, `C_3b`).
-/

namespace EntropyBounds.GlueZ.Certs.C3BALL

variable {G : Type} [AddCommGroup G] [DecidableEq G]

open EntropyBounds.Iid EntropyBounds.GlueG EntropyBounds.GlueZ SumsDifferences SumsDifferences.NonShannon

theorem cf_ineq (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (CF Γ p).H L603 ≤ (882 / 1259 : ℝ) * (CF Γ p).H L1 + (1609 / 2518 : ℝ) * (CF Γ p).H L6 + (2467 / 5036 : ℝ) * (CF Γ p).H L18 := by
  rw [i349 h, i0 h, i2 h, i7 h]
  have h0 := row0 Γ p h
  have h1 := row1 Γ p h
  have h2 := row2 Γ p h
  have h3 := row3 Γ p h
  have h4 := row4 Γ p h
  have h5 := row5 Γ p h
  have h6 := row6 Γ p h
  have h7 := row7 Γ p h
  have h8 := row8 Γ p h
  have h9 := row9 Γ p h
  have h10 := row10 Γ p h
  have h11 := row11 Γ p h
  have h12 := row12 Γ p h
  have h13 := row13 Γ p h
  have h14 := row14 Γ p h
  have h15 := row15 Γ p h
  have h16 := row16 Γ p h
  have h17 := row17 Γ p h
  have h18 := row18 Γ p h
  have h19 := row19 Γ p h
  have h20 := row20 Γ p h
  have h21 := row21 Γ p h
  have h22 := row22 Γ p h
  have h23 := row23 Γ p h
  have h24 := row24 Γ p h
  have h25 := row25 Γ p h
  have h26 := row26 Γ p h
  have h27 := row27 Γ p h
  have h28 := row28 Γ p h
  have h29 := row29 Γ p h
  have h30 := row30 Γ p h
  have h31 := row31 Γ p h
  have h32 := row32 Γ p h
  have h33 := row33 Γ p h
  have h34 := row34 Γ p h
  have h35 := row35 Γ p h
  have h36 := row36 Γ p h
  have h37 := row37 Γ p h
  have h38 := row38 Γ p h
  have h39 := row39 Γ p h
  have h40 := row40 Γ p h
  have h41 := row41 Γ p h
  have h42 := row42 Γ p h
  have h43 := row43 Γ p h
  have h44 := row44 Γ p h
  have h45 := row45 Γ p h
  have h46 := row46 Γ p h
  have h47 := row47 Γ p h
  have h48 := row48 Γ p h
  have h49 := row49 Γ p h
  have h50 := row50 Γ p h
  have h51 := row51 Γ p h
  have h52 := row52 Γ p h
  have h53 := row53 Γ p h
  have h54 := row54 Γ p h
  have h55 := row55 Γ p h
  have h56 := row56 Γ p h
  have h57 := row57 Γ p h
  have h58 := row58 Γ p h
  have h59 := row59 Γ p h
  have h60 := row60 Γ p h
  have h61 := row61 Γ p h
  have h62 := row62 Γ p h
  have h63 := row63 Γ p h
  have h64 := row64 Γ p h
  have h65 := row65 Γ p h
  have h66 := row66 Γ p h
  have h67 := row67 Γ p h
  have h68 := row68 Γ p h
  have h69 := row69 Γ p h
  have h70 := row70 Γ p h
  have h71 := row71 Γ p h
  have h72 := row72 Γ p h
  have h73 := row73 Γ p h
  have h74 := row74 Γ p h
  have h75 := row75 Γ p h
  have h76 := row76 Γ p h
  have h77 := row77 Γ p h
  have h78 := row78 Γ p h
  have h79 := row79 Γ p h
  have h80 := row80 Γ p h
  have h81 := row81 Γ p h
  have h82 := row82 Γ p h
  have h83 := row83 Γ p h
  have h84 := row84 Γ p h
  have h85 := row85 Γ p h
  have h86 := row86 Γ p h
  have h87 := row87 Γ p h
  have h88 := row88 Γ p h
  have h89 := row89 Γ p h
  have h90 := row90 Γ p h
  have h91 := row91 Γ p h
  have h92 := row92 Γ p h
  have h93 := row93 Γ p h
  have h94 := row94 Γ p h
  have h95 := row95 Γ p h
  have h96 := row96 Γ p h
  have h97 := row97 Γ p h
  have h98 := row98 Γ p h
  have h99 := row99 Γ p h
  have h100 := row100 Γ p h
  have h101 := row101 Γ p h
  have h102 := row102 Γ p h
  have h103 := row103 Γ p h
  have h104 := row104 Γ p h
  have h105 := row105 Γ p h
  have h106 := row106 Γ p h
  have h107 := row107 Γ p h
  have h108 := row108 Γ p h
  have h109 := row109 Γ p h
  have h110 := row110 Γ p h
  have h111 := row111 Γ p h
  have h112 := row112 Γ p h
  have h113 := row113 Γ p h
  have h114 := row114 Γ p h
  have h115 := row115 Γ p h
  have h116 := row116 Γ p h
  have h117 := row117 Γ p h
  have h118 := row118 Γ p h
  have h119 := row119 Γ p h
  have h120 := row120 Γ p h
  have h121 := row121 Γ p h
  have h122 := row122 Γ p h
  have h123 := row123 Γ p h
  have h124 := row124 Γ p h
  have h125 := row125 Γ p h
  have h126 := row126 Γ p h
  have h127 := row127 Γ p h
  have h128 := row128 Γ p h
  have h129 := row129 Γ p h
  have h130 := row130 Γ p h
  have h131 := row131 Γ p h
  have h132 := row132 Γ p h
  have h133 := row133 Γ p h
  have h134 := row134 Γ p h
  have h135 := row135 Γ p h
  have h136 := row136 Γ p h
  have h137 := row137 Γ p h
  have h138 := row138 Γ p h
  have h139 := row139 Γ p h
  have h140 := row140 Γ p h
  have h141 := row141 Γ p h
  have h142 := row142 Γ p h
  have h143 := row143 Γ p h
  have h144 := row144 Γ p h
  have h145 := row145 Γ p h
  have h146 := row146 Γ p h
  have h147 := row147 Γ p h
  have h148 := row148 Γ p h
  have h149 := row149 Γ p h
  have h150 := row150 Γ p h
  have h151 := row151 Γ p h
  have h152 := row152 Γ p h
  have h153 := row153 Γ p h
  have h154 := row154 Γ p h
  have h155 := row155 Γ p h
  have h156 := row156 Γ p h
  have h157 := row157 Γ p h
  have h158 := row158 Γ p h
  have h159 := row159 Γ p h
  have h160 := row160 Γ p h
  have h161 := row161 Γ p h
  have h162 := row162 Γ p h
  linear_combination ((38 : ℝ) / 1259) * h0 + ((73 : ℝ) / 2518) * h1 + ((147 : ℝ) / 5036) * h2 + ((41 : ℝ) / 2518) * h3 + ((35 : ℝ) / 2518) * h4 + ((101 : ℝ) / 2518) * h5 + ((23 : ℝ) / 1259) * h6 + ((71 : ℝ) / 5036) * h7 + ((1 : ℝ) / 1259) * h8 + ((107 : ℝ) / 5036) * h9 + ((24 : ℝ) / 1259) * h10 + ((37 : ℝ) / 2518) * h11 + ((3 : ℝ) / 2518) * h12 + ((753 : ℝ) / 5036) * h13 + ((66 : ℝ) / 1259) * h14 + ((751 : ℝ) / 5036) * h15 + ((7 : ℝ) / 2518) * h16 + ((75 : ℝ) / 5036) * h17 + ((2 : ℝ) / 1259) * h18 + ((23 : ℝ) / 1259) * h19 + ((3 : ℝ) / 2518) * h20 + ((19 : ℝ) / 2518) * h21 + ((11 : ℝ) / 1259) * h22 + ((29 : ℝ) / 5036) * h23 + ((99 : ℝ) / 5036) * h24 + ((1 : ℝ) / 1259) * h25 + ((101 : ℝ) / 2518) * h26 + ((1 : ℝ) / 1259) * h27 + ((37 : ℝ) / 2518) * h28 + ((3 : ℝ) / 1259) * h29 + ((3 : ℝ) / 2518) * h30 + ((37 : ℝ) / 2518) * h31 + ((31 : ℝ) / 2518) * h32 + ((30 : ℝ) / 1259) * h33 + ((4 : ℝ) / 1259) * h34 + ((3 : ℝ) / 2518) * h35 + ((13 : ℝ) / 5036) * h36 + ((1 : ℝ) / 1259) * h37 + ((25 : ℝ) / 2518) * h38 + ((3 : ℝ) / 1259) * h39 + ((21 : ℝ) / 2518) * h40 + ((4 : ℝ) / 1259) * h41 + ((19 : ℝ) / 2518) * h42 + ((2 : ℝ) / 1259) * h43 + ((17 : ℝ) / 1259) * h44 + ((19 : ℝ) / 2518) * h45 + ((71 : ℝ) / 5036) * h46 + ((35 : ℝ) / 2518) * h47 + ((3 : ℝ) / 2518) * h48 + ((57 : ℝ) / 2518) * h49 + ((51 : ℝ) / 2518) * h50 + ((41 : ℝ) / 2518) * h51 + ((13 : ℝ) / 5036) * h52 + ((31 : ℝ) / 2518) * h53 + ((3 : ℝ) / 2518) * h54 + ((1 : ℝ) / 1259) * h55 + ((1 : ℝ) / 1259) * h56 + ((73 : ℝ) / 2518) * h57 + ((3 : ℝ) / 2518) * h58 + ((11 : ℝ) / 2518) * h59 + ((17 : ℝ) / 2518) * h60 + ((4 : ℝ) / 1259) * h61 + ((31 : ℝ) / 2518) * h62 + ((19 : ℝ) / 2518) * h63 + ((1 : ℝ) / 1259) * h64 + ((3 : ℝ) / 2518) * h65 + ((4 : ℝ) / 1259) * h66 + ((28 : ℝ) / 1259) * h67 + ((41 : ℝ) / 2518) * h68 + ((21 : ℝ) / 2518) * h69 + ((4 : ℝ) / 1259) * h70 + ((1 : ℝ) / 1259) * h71 + ((1 : ℝ) / 1259) * h72 + ((3 : ℝ) / 1259) * h73 + ((1 : ℝ) / 1259) * h74 + ((11 : ℝ) / 1259) * h75 + ((3 : ℝ) / 2518) * h76 + ((13 : ℝ) / 5036) * h77 + ((4 : ℝ) / 1259) * h78 + ((31 : ℝ) / 2518) * h79 + ((17 : ℝ) / 1259) * h80 + ((1 : ℝ) / 1259) * h81 + ((1 : ℝ) / 1259) * h82 + ((1 : ℝ) / 1259) * h83 + ((11 : ℝ) / 2518) * h84 + ((13 : ℝ) / 5036) * h85 + ((1 : ℝ) / 1259) * h86 + ((1 : ℝ) / 1259) * h87 + ((3 : ℝ) / 1259) * h88 + ((19 : ℝ) / 2518) * h89 + ((49 : ℝ) / 5036) * h90 + ((30 : ℝ) / 1259) * h91 + ((19 : ℝ) / 2518) * h92 + ((41 : ℝ) / 2518) * h93 + ((31 : ℝ) / 2518) * h94 + ((1 : ℝ) / 1259) * h95 + ((21 : ℝ) / 1259) * h96 + ((4 : ℝ) / 1259) * h97 + ((1 : ℝ) / 1259) * h98 + ((19 : ℝ) / 2518) * h99 + ((3 : ℝ) / 2518) * h100 + ((37 : ℝ) / 2518) * h101 + ((4 : ℝ) / 1259) * h102 + ((31 : ℝ) / 2518) * h103 + ((6 : ℝ) / 1259) * h104 + ((25 : ℝ) / 2518) * h105 + ((27 : ℝ) / 2518) * h106 + ((19 : ℝ) / 2518) * h107 + ((1 : ℝ) / 1259) * h108 + ((3 : ℝ) / 2518) * h109 + ((3 : ℝ) / 2518) * h110 + ((1 : ℝ) / 1259) * h111 + ((3 : ℝ) / 1259) * h112 + ((2 : ℝ) / 1259) * h113 + ((17 : ℝ) / 1259) * h114 + ((1 : ℝ) / 1259) * h115 + ((2 : ℝ) / 1259) * h116 + ((29 : ℝ) / 1259) * h117 + ((19 : ℝ) / 2518) * h118 + ((3 : ℝ) / 1259) * h119 + ((1 : ℝ) / 1259) * h120 + ((3 : ℝ) / 2518) * h121 + ((3 : ℝ) / 2518) * h122 + ((3 : ℝ) / 2518) * h123 + ((1 : ℝ) / 1259) * h124 + ((3 : ℝ) / 2518) * h125 + ((1 : ℝ) / 1259) * h126 + ((4 : ℝ) / 1259) * h127 + ((1 : ℝ) / 1259) * h128 + ((1 : ℝ) / 1259) * h129 + ((1 : ℝ) / 1259) * h130 + ((19 : ℝ) / 2518) * h131 + ((3 : ℝ) / 2518) * h132 + ((3 : ℝ) / 1259) * h133 + ((3 : ℝ) / 1259) * h134 + ((1 : ℝ) / 1259) * h135 + ((1 : ℝ) / 1259) * h136 + ((28 : ℝ) / 1259) * h137 + ((2 : ℝ) / 1259) * h138 + ((2403 : ℝ) / 5036) * h139 + ((793 : ℝ) / 5036) * h140 + ((313 : ℝ) / 2518) * h141 + ((1615 : ℝ) / 5036) * h142 + ((537 : ℝ) / 2518) * h143 + ((-2481 : ℝ) / 5036) * h144 + ((311 : ℝ) / 5036) * h145 + ((279 : ℝ) / 5036) * h146 + ((85 : ℝ) / 2518) * h148 + ((-223 : ℝ) / 1259) * h150 + ((28 : ℝ) / 1259) * h151 + ((67 : ℝ) / 2518) * h152 + ((141 : ℝ) / 5036) * h153 + ((60 : ℝ) / 1259) * h154 + ((165 : ℝ) / 2518) * h155 + ((-4 : ℝ) / 1259) * h156 + ((32 : ℝ) / 1259) * h157 + ((-31 : ℝ) / 2518) * h158 + ((-154 : ℝ) / 1259) * h159 + ((34 : ℝ) / 1259) * h160 + ((3 : ℝ) / 2518) * h161 + ((3 : ℝ) / 2518) * h162

theorem entropy_ineq (Γ : Finset (G × G)) (p : G × G → ℝ) (hinj : Inj Γ)
    (hp : ∀ q ∈ Γ, 0 ≤ p q)
    (hs : ∑ q ∈ Γ, p q = 1) :
    pushEntropy Γ p (fun q => q) ≤ (882 / 1259 : ℝ) * pushEntropy Γ p (fun q => q.1) + (1609 / 2518 : ℝ) * pushEntropy Γ p (fun q => q.2)
      + (2467 / 5036 : ℝ) * pushEntropy Γ p (fun q => q.1 + q.2) := by
  have h : HypZ Γ p := ⟨hinj, hp, hs⟩
  have key := cf_ineq Γ p h
  rw [lift0 h L603 (by decide) (by decide) (by decide), lift0 h L1 (by decide) (by decide) (by decide), lift0 h L6 (by decide) (by decide) (by decide), lift0 h L18 (by decide) (by decide) (by decide)] at key
  rw [show L603 = [F1, F5] from rfl, H_base_pairB hp F1 F5 0 (by decide) (by decide),
    show L1 = [F1] from rfl, H_base_xB hp F1 0 (by decide),
    show L6 = [F5] from rfl, H_base_yB hp F5 0 (by decide),
    show L18 = [F14] from rfl, H_base_sumB hp F14 0 (by decide)] at key
  exact key

theorem set_ineq (A B : Finset G) (P : Finset (G × G))
    (hP : P ⊆ A ×ˢ B) :
    (#(P.image fun q => q.1 - q.2) : ℝ)
      ≤ (max (max (#A : ℝ) (#B : ℝ)) (#(P.image fun q => q.1 + q.2) : ℝ)) ^ ((882 / 1259 : ℝ) + (1609 / 2518 : ℝ) + (2467 / 5036 : ℝ)) :=
  set_form (by norm_num) (by norm_num) (by norm_num) (fun Γ p hinj hp hs => entropy_ineq Γ p hinj hp hs) A B P hP

theorem set_ineq' (A B : Finset G) (P : Finset (G × G))
    (hP : P ⊆ A ×ˢ B) :
    (#(P.image fun q => q.1 - q.2) : ℝ)
      ≤ (max (max (#A : ℝ) (#B : ℝ)) (#(P.image fun q => q.1 + q.2) : ℝ)) ^ (9213 / 5036 : ℝ) := by
  have e : (882 / 1259 : ℝ) + (1609 / 2518 : ℝ) + (2467 / 5036 : ℝ) = (9213 / 5036 : ℝ) := by norm_num
  rw [← e]
  exact set_ineq A B P hP

end EntropyBounds.GlueZ.Certs.C3BALL
