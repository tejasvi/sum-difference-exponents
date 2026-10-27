# Certified upper bounds for two sum-difference exponents

Certificates, checkers and search programs for the paper
*Certified upper bounds for two sum-difference exponents* by Tejasvi Singh Tomar
(Zenodo, [doi:10.5281/zenodo.23687855](https://doi.org/10.5281/zenodo.23687855)).

## Results

For finite subsets `A`, `B` of an abelian group and `G ⊆ A × B`, write `A +_G B = {a + b : (a, b) ∈ G}` and
`A −_G B = {a − b : (a, b) ∈ G}`.

1. **Theorem 1.1.** For random variables `X`, `Y` with finitely many values in a torsion-free abelian group,
   `H(X − Y) ≤ λ_X H(X) + λ_Y H(Y) + λ_S H(X + Y)`, and `|A −_G B| ≤ |A|^λ_X |B|^λ_Y |A +_G B|^λ_S`, where

       λ_X = 925252334339885103560423126733856553/1309548008918246261431347658091038786,
       λ_Y = 424585766727935297449756583005066048/654774004459123130715673829045519393,
       λ_S = 1237016505223052067896560048548494601/2619096017836492522862695316182077572.

   The sum is 4785864240814563464816432634036471899/2619096017836492522862695316182077572
   < 1.8272963, so the Kakeya-type sum-difference constant `C_3b` (Problem 6.30 of Georgiev, Gómez-Serrano, Tao
   and Wagner, arXiv:2511.02864) is at most 1.8272963. The previous bound was 11/6 (Katz and Tao, 1999).
   The certificate divides only by 2, so these statements hold in every abelian group without 2-torsion. It is
   self-contained: every non-Shannon inequality it uses is proved inside it from the copy lemma.
2. **Theorem 1.2.** The same statements hold in every abelian group with
   `(λ_X, λ_Y, λ_S) = (882/1259, 1609/2518, 2467/5036)`, whose sum is 9213/5036 < 1.8294282.
3. **Theorem 1.3.** For finite subsets `X`, `Y` of a torsion-free abelian group, `|X − Y| ≤ |X + Y|^λ` with
   `λ = 20486493787/14418560416 < 1.42084184`, proved with Shannon inequalities only. With Kleinwaks' transfer theorem
   (proved in the paper), the sum-difference constant `C_3a` of Gyarmati, Hennecart and Ruzsa (Problem 6.44)
   satisfies `C_3a ≤ 26554427158/20486493787 < 1.29619190`.
4. **Erdős problem #1097.** A set of `n` integers determines at most `n^1.8272963` distinct positive common
   differences of three-term arithmetic progressions (Remark 1.5).

## Checking the certificates

The checkers need only Python 3 and its standard library.

    python3 checker/check630.py certs/c3b_torsionfree.json   # Theorem 1.1
    python3 checker/check630.py certs/c3b_allgroups.json     # Theorem 1.2
    python3 checker/check630.py certs/c3b_short.json         # Appendix A, 841/459
    python3 checker/check630.py certs/c3b_katz_tao.json      # Proposition 3.2, 11/6
    python3 checker/check3.py certs/pair_exponent.json       # Theorem 1.3

Each run prints `PASS` and the proved constant, and exits with status 0 on success. The checkers refuse to run
under `python -O`, because they rely on assert statements. The checks take seconds.

| file | proves | SHA-256 |
| --- | --- | --- |
| `certs/c3b_torsionfree.json` | Theorem 1.1 | `2f5536517aa1b928229bc88b4cf3fcdc19e09a591aa0dcaadb9bb4b0e24de614` |
| `certs/c3b_allgroups.json` | Theorem 1.2 | `a7d47d40bccd60cc507d72be161eeecd22193c29146820d45fa2fec2c3f2391a` |
| `certs/c3b_short.json` | Appendix A | `244f0ff7dc5eadcc2d0f05ac0e6e44ff664a0bf8487c4a398f7d2fed785ab8b5` |
| `certs/c3b_katz_tao.json` | Proposition 3.2 | `9411facabf6a695b1880fbe3560aec5d343fa38815340a352acc8e194e65b7e2` |
| `certs/pair_exponent.json` | Theorem 1.3 | `772f2c701d2a1eab4a5c5e28e3874174d78d583382af6adf49b1edec515daa3f` |
| `checker/check630.py` | | `a9fc801318ed263a6a75c877370e1753f6c7b8594536aa4fab8eea088dee6a97` |
| `checker/check3.py` | | `0b2f143e320dd859560691406ce15ec10a2c429857d901efd3f7b97a2c54dac0` |

`SHA256SUMS` lists the SHA-256 of every other file (`sha256sum -c SHA256SUMS` checks them). `paper/main.tex` is the LaTeX source of the paper.

### What the checkers verify

`checker/check630.py` reads a certificate for the Kakeya-type exponent: the copy steps of the configuration
(Section 3.2 of the paper), the cross forms as integer vectors in the twelve coordinates
`x0, y0, x1, y1, ..., x5, y5`, the equal-law identifications, the rows and the numbers `λ`. It recomputes the
relations of each copy step from the copy lemma and the closure of every set of forms, that is, the smallest
subspace over Q that contains the forms and the relations, and that contains `x_v` and `y_v` whenever it contains
`x_v − y_v`. It also recomputes every row
from its definition: Shannon rows `I(i; j | K) ≥ 0` and `H(K, i) − H(K) ≥ 0`, the conditional-independence identity of each
copy step, Matúš's inequality `M_s(a, b, c, d) ≥ 0` for integers `s ≥ 1`, and applications of inequalities proved
inside the certificate. Each such inequality (a "lemma") comes with its own copy steps and the multipliers of
Shannon inequalities, copy identities and earlier lemmas that prove it; the checker verifies every lemma before it
is used and rejects cycles. It checks that the weighted rows give
`H(X, Y) ≤ λ_X H(X) + λ_Y H(Y) + λ_S H(X + Y)` as an exact identity in rational arithmetic, and it rejects
negative weights on inequality rows.

`checker/check3.py` reads a certificate for the two-set exponent: two independent copies `D0`, `D1` of
Kleinwaks' coupling, further independent variables with prescribed laws `μ^{*i} * ν^{*j}`, the reflected
configuration, and the grid values `h(i, j)` up to depth 12. For Theorem 1.3 the further variables are three
variables `w`, `v`, `u` with the law `μ` of the first marginal. The checker rebuilds
the closures, the independence identities, the symmetry identities, the identifications of sums of independent
variables with grid values, the support rows and the grid rows. For the symmetry identities it checks that each
permutation maps the pairs `D0`, `D1` to each other and each extra variable to one of the same law. For the partial
symmetries and partial reflections, (R8) and (R9) in the paper, it checks that the coordinates of each independent
block (`D0`, `D1` or an extra variable) that occur in the row are mapped into a single block, different blocks into
different blocks, with equal laws, or for partial reflections with negated coordinates and transposed laws. It then checks that the
weighted rows sum exactly to `λ log|X + Y| − log|X − Y|`. The checker also accepts row types that Theorem 1.3 does
not use: non-Shannon rows, rows that identify the reflected configuration as a whole with the original one (`rshare`,
`share`), conditional copies with their rows, and further support and grid families.

### Further checks

These scripts need `python-flint`, `numpy` and `scipy`.

- `independent/indep_check.py`, `independent/indep3.py`: second checkers, written independently from the
  mathematical definitions; they use an explicit parametrization of the configuration and closures as reduced
  row echelon bases. Usage: `python3 independent/indep_check.py CERT` and `python3 independent/indep3.py CERT --strict-ci`.
- `independent/diff_closures.py CERT`: compares the relations and closures computed by the two checkers.
- For certificates with lemmas (`certs/c3b_torsionfree.json`) there are further scripts.
  `independent/indep_check2.py CERT` is the second checker extended by a re-implementation of the lemma check of
  `checker/check630.py` (`independent/lemma_verify.py`). `independent/diff_closures2.py CERT` and
  `independent/division_check3.py CERT` include the closures of the lemma rows. `independent/neg_tests6.py CERT`
  adds perturbations of the lemmas to the negative tests below. `independent/numeric_validate_lemma.py CERT N SEED`
  evaluates the rows, lemma rows included, on explicit joint laws. `independent/matus_check.py CERT` checks the chain of Matúš lemmas against the
  published formula. `independent/dfz_lp.py CERT` re-derives each lemma from the list of Dougherty, Freiling and
  Zeger from its own copy specification by an exact linear program, and `independent/dfz_paper_cmp.py CERT DFZ.txt`
  compares these lemmas with Section VIII of arXiv:1104.3602 (`DFZ.txt` is `pdftotext -layout` of that paper, not
  included here).
- `independent/division_check.py CERT`, `independent/division_check2.py CERT`, `independent/div643.py CERT`: for
  every set of forms in a certificate, compare the closure over Q with the closures over Z and over Z[1/m].
- `independent/matus_lp.py 30`, `independent/matus_param.py SMAX`: exact certificates of the inductive step of
  Matúš's family: for `s ≤ 30` by linear programming, and for `2 ≤ s ≤ SMAX` by an identity whose coefficients are
  polynomials in `s`.
- `independent/neg_tests5.py CERT`, `independent/neg643.py CERT`: perturbed certificates. Both checkers reject
  them, except perturbations that leave a valid certificate, such as dropping an identification that the identity
  does not use or replacing a cross form by its negative or by its double (Table 7 of the paper).
- `independent/numeric_validate.py CERT N SEED`, `independent/val643.py CERT N SEED`: evaluation of every row on
  explicit joint laws, namely random laws and the 13-point law of the record lower bound for `C_3b`, and on explicit
  sets `X`, `Y` for the two-set exponent. `val643.py` also runs fixed pairs, among them one with 43,264 atoms per
  copy, which take more than an hour. The 13-point law is not included here: download
  `certificate_3b_13pt.json` from its archive, [doi:10.5281/zenodo.20794135](https://doi.org/10.5281/zenodo.20794135),
  and set the environment variable `MI13_LAW` to its path.
- `python3 tools/split_pair.py checker/check3.py certs/pair_exponent.json`: splits the certificate of Theorem 1.3
  into the configuration inequality (Proposition 4.1) and the grid inequality (Lemma 4.2), prints their sum and
  counts the closed sets used (Table 1).
- `python3 tools/verify_appendix_a.py checker/check630.py tools/appendix_a_rows.tex tools/appendix_a_identifications.tex`:
  checks the identity (A.1) of Appendix A directly from the tables printed in the paper.
- `python3 tools/stats630.py checker/check630.py CERT`: counts the closed sets used by a certificate of
  Section 3 (Table 1).

## Lean proofs

`lean/` contains Lean 4 proofs, checked by the Lean kernel, of the following statements. All of them depend only on
the axioms `propext`, `Classical.choice` and `Quot.sound`, as the `#print axioms` lines of `lean/Axioms.lean` show.
The lines for the theorems of Theorem 1.2 were run on their own. The other lines, and every Lean file outside
`lean/EntropyBounds/GlueZ/` except `Axioms.lean`, are unchanged since commit `b3786a3` of this repository, whose build
checked them. The theorems do not
mention the certificates, so the programs that translate the certificates into Lean need not be trusted.

The Lean files in the namespace `EntropyBounds.Glue.Certs.CL3B6SC` (certificate `certs/c3b_torsionfree.json`, Theorem 1.1) prove

- `entropy_ineq`: for every finite `Γ ⊆ ℝ × ℝ` on which `(x, y) ↦ x − y` is injective and every probability
  weight `p` on `Γ`, the pair `(X, Y)` with law `p` satisfies `H(X, Y) ≤ λ_X H(X) + λ_Y H(Y) + λ_S H(X + Y)` with
  the numbers `λ` of the certificate;
- `entropy_ineq_general`: for every finitely supported pair `(X, Y)` of real random variables,
  `H(X − Y) ≤ λ_X H(X) + λ_Y H(Y) + λ_S H(X + Y)` (Theorem 1.1(a); its proof formalizes Lemma 3.1(a));
- `entropy_max`: `H(X − Y) ≤ C max(H(X), H(Y), H(X + Y))`;
- `set_ineq'`: for finite `A, B ⊆ ℝ` and `G ⊆ A × B`, `#(A −_G B) ≤ max(#A, #B, #(A +_G B)) ^ C`;
- `set_ineq_prod` (file `Product.lean`): for finite `A, B ⊆ ℝ` and `G ⊆ A × B`,
  `#(A −_G B) ≤ #A ^ λ_X · #B ^ λ_Y · #(A +_G B) ^ λ_S` (Theorem 1.1(b) over ℝ),

where `C = 4785864240814563464816432634036471899 / 2619096017836492522862695316182077572`. Each inequality that the
certificate proves inside itself (a "lemma") becomes a Lean theorem about arbitrary random variables, proved from its
own copy steps.

The Lean files in the namespace `EntropyBounds.GlueG.Certs.CL3B6SC` translate the same certificate for an arbitrary
abelian group `G : Type` without 2-torsion (hypothesis `∀ x : G, x + x = 0 → x = 0`), with closures computed over
ℤ[1/2]. They prove `entropy_ineq_general`, `entropy_max`, `set_ineq'` and `set_ineq_prod` in `G` (Theorem 1.1(a)
and (b) in every abelian group without 2-torsion), the versions for torsion-free groups
`entropy_ineq_general_torsionFree`, `set_ineq'_torsionFree` and `set_ineq_prod_torsionFree`, and
`bridge_entropy_ineq`, `bridge_entropy_ineq_general`, `bridge_set_ineq'` and `bridge_set_ineq_prod`, which give the
statements over ℝ of the same names above. `Erdos1097.lean` proves `ap_differences_card_le`:
a finite set `A` in such a group determines at most `#A ^ C` nonzero common differences of three-term arithmetic
progressions, and `ap_differences_pos_card_le_int`: the same for positive differences and finite `A ⊆ ℤ`.

The Lean files in the namespace `EntropyBounds.GlueZ.Certs.C3BALL` (certificate `certs/c3b_allgroups.json`, Theorem 1.2) translate this
certificate for an arbitrary abelian group `G : Type`. The certificate does not divide, so the closures are computed
over ℤ. They prove `entropy_ineq_general` and `entropy_max` in `G`, and the hand-written
`lean/EntropyBounds/GlueZ/Thm12.lean` proves `thm12_entropy` and `thm12_set` in `G`: statements (a) and (b) of
Theorem 1.1 with the numbers of Theorem 1.2, that is, Theorem 1.2, in every abelian group, and `lambda_sum`: the
three numbers sum to 9213/5036 < 1.8294282.

The Lean files in the namespace `EntropyBounds.TwoSet.Certs.R7A5` (certificate `certs/pair_exponent.json`, Theorem 1.3) prove

- `pair_ceiling : ∀ X Y : Finset ℤ, #(X - Y) ≤ #(X + Y) ^ (20486493787 / 14418560416)` (as real numbers);
- `pair_ceiling_torsionFree` (file `TorsionFree.lean` in that directory): the same inequality for finite subsets
  `X, Y` of any torsion-free abelian group, deduced from `pair_ceiling` by `card_sub_le_of_int`
  (`lean/EntropyBounds/TwoSet/TorsionFree.lean`), a formal version of the reduction to ℤ in the proof of Theorem 1.3;
- `theta_le : theta ≤ 26554427158 / 20486493787`, where `theta` is the exponent of Gyarmati, Hennecart and Ruzsa in
  Kleinwaks' definition, with a constant `c(K) > 0` for every `K > 1`;
- `thetaK_le : thetaK ≤ 26554427158 / 20486493787`, where `thetaK` is the same supremum with `K` and `c` fixed along
  the sequence of sets, as on page 3a of Tao's list of optimization constants;
- `admissibleK_le_value` (file `Headline.lean` in that directory): every exponent that is admissible with `K` and
  `c` fixed is at most 26554427158 / 20486493787.

The rows for partial symmetries and partial reflections are realized by permutations of independent copies of
Kleinwaks' coupling (after the reflection, for partial reflections), and the kernel checks by evaluation that each
permutation carries the forms of a row to their images.

Files:

- `lean/SumDifference/`: the Lean library of L. J. Kleinwaks, *Improved sum-difference inequalities in abelian
  groups* (https://github.com/kleinwaks/sum-difference, commit 3664fd11b28ee7a4ac398e951156525bc05b08fa,
  Apache-2.0), ported to Lean v4.35.0-rc3 and Mathlib `c55e6e786f49`. Each modified file lists its changes at the top;
  the statements are unchanged. See `lean/NOTICE` and `lean/third_party/kleinwaks_sum_difference/`.
- `lean/EntropyBounds/Glue/`: the configuration of Section 3.2, with copy steps built from Kleinwaks' copy-lemma
  construction, its relations and the closures modulo the relations; the passage from the entropy inequality to the
  set inequality, in the max form and in the product form (`SetFormProd.lean`); and the reduction to pairs with
  `x − y` injective (`Shuffle.lean`).
- `lean/EntropyBounds/GlueG/`: the same for coordinates in an abelian group without 2-torsion, with the theorems
  `bridge_*` back to ℝ (`BridgeCL3B6SC.lean`) and the corollary for Erdős problem #1097 (`Erdos1097.lean`).
- `lean/EntropyBounds/GlueZ/`: the witness checks of GlueG with every multiplier 1, which need no hypothesis on doubling
  (`Basic.lean`), and the two theorems for Theorem 1.2 (`Thm12.lean`).
- `lean/EntropyBounds/Lemma/`: inequalities proved by copy steps, for arbitrary random variables.
- `lean/EntropyBounds/Iid/`, `lean/EntropyBounds/TwoSet/Common.lean`, `lean/EntropyBounds/TwoSet/Mirror.lean`:
  lemmas about independent copies of Kleinwaks' coupling, one for each kind of row of the two-set certificate
  format, where the reflected configuration is realized on the same copies, and the bound for `thetaK`.
- `lean/EntropyBounds/TwoSet/TorsionFree.lean`: the transfer from ℤ to torsion-free abelian groups.
- `lean/EntropyBounds/TwoSet/Headline.lean`: the bound `θ ≤ 2 − 1/λ` for every exponent `θ` that is admissible with
  `K` and `c` fixed, from `|X − Y| ≤ |X + Y|^λ` for all finite `X, Y ⊆ ℤ` (`admissibleK_le_of_pair_ceiling`, no
  supremum involved), and the facts that make `thetaK` the supremum of a nonempty bounded set (`admissibleK_one`,
  `bddAbove_admissibleK`).
- `lean/EntropyBounds/Glue/Certs/CL3B6SC/`, `lean/EntropyBounds/GlueG/Certs/CL3B6SC/`,
  `lean/EntropyBounds/GlueZ/Certs/C3BALL/` and
  `lean/EntropyBounds/TwoSet/Certs/R7A5/`: the certificates translated into Lean by `lean/tools/export_glue.py` (with
  `export_lemmas.py`, and `export_product.py` for `Product.lean`), `lean/tools/export_glue_g.py`,
  `lean/tools/export_glue_z.py` and `lean/tools/export_twoset_x.py`, which use other versions of the checkers as
  libraries (`lean/tools/ref/`: `check630.py` 711d7e41 and `check3_8ab8e59a.py`). In `lean/`, the commands

      python3 tools/export_glue.py ../certs/c3b_torsionfree.json CL3B6SC
      python3 tools/export_product.py CL3B6SC
      python3 tools/export_glue_g.py ../certs/c3b_torsionfree.json CL3B6SC
      python3 tools/export_twoset_x.py ../certs/pair_exponent.json R7A5
      python3 tools/export_glue_z.py ../certs/c3b_allgroups.json C3BALL

  regenerate these files byte for byte. Move the four directories elsewhere first: `export_glue_z.py` refuses to write
  into an existing directory.

To build (the toolchain is installed by `elan` from `lean/lean-toolchain`):

    cd lean
    lake exe cache get          # prebuilt Mathlib
    lake build
    lake env lean Axioms.lean   # prints the axioms and the statements of the theorems above

## Search programs

The certificates were found with the programs in `search/`. They need `numpy`, `scipy`, `highspy`, `python-flint`
and `numba` (we used Python 3.12 with numpy 2.5.4, scipy 1.18.1, highspy 1.15.1, python-flint 0.9.0 and numba
0.68.0), and they are not needed for checking.

- `search/kakeya/`: the entropy linear program on the configuration of Section 3.2 (`eng.py`, `fastlp.py`),
  exact certificate extraction (`cert_fast.py`), cutting planes for Matúš's inequalities (`nonshannon.py`,
  `sepnb.py`, `ns_cert.py`), and greedy selection of cross forms (`fwdsel.py`, `fwdmatus.py`). In `search/kakeya/`,
  after `mkdir certs`, `python3 mkcert_mech.py inputs/fs116a_forms.json certs/x116b.json` writes, in a few minutes,
  a file identical byte for byte to `certs/c3b_allgroups.json` (Theorem 1.2).
- `search/kakeya_lemma/`: the search for inequalities proved by the copy lemma. `clexp.py` adds rounds of
  copy-lemma separation to a linear program on the configuration: for the most Ingleton-violating quadruples of
  closed sets and each copy scheme of the list of Dougherty, Freiling and Zeger, `clsep.py` finds the most violated
  inequality that the scheme proves and turns the optimal vertex into an exact lemma. `dfzlemma.py` proves the
  inequalities of that list from their copy schemes (`dfz/lemmas.json`), and `matuslemma.py` writes the chain of
  Matúš lemmas (`dfz/matus_lemmas.json`). The 43 forms of `inputs/fm116r3_forms.json` and the 6921 inequalities of
  `inputs/cl3b_cuts.json` (5749 instances of Matúš's inequalities, 1165 instances of 47 entries of the list and 7
  instances of 6 lemmas found by `clexp.py`, recorded in `inputs/cl3b_lemmas.json`) are the output of the search.
  The search is not reproducible byte for byte, because the parallel separation keeps the most violated
  inequalities by their floating-point values. In `search/kakeya_lemma/`, after `mkdir certs`, the command
  `python3 certify_fcd.py cl3b6 inputs/fm116r3_forms.json inputs/cl3b_cuts.json` solves the linear program with
  these inequalities and writes, in about two minutes, the exact certificate `certs/cl3b6.json`, identical byte for
  byte to `inputs/cl3b6.json`, which uses Matúš's inequalities as rows. Then
  `python3 selfcontain.py inputs/cl3b6.json OUT.json` replaces those rows by applications of the Matúš lemmas and
  writes a file identical byte for byte to `certs/c3b_torsionfree.json` (Theorem 1.1).
- `search/short/`: the short certificate of Appendix A (`latrows.py`, `milp.py`) for the forms in
  `inputs/q5_forms.json`.
- `search/pair/`: the linear program for the two-set exponent (`eng2.py`, `eng643.py`), row generation
  (`rowgen.py`), column generation on the certificate linear program (`colgen.py`), exact certificate extraction
  (`cert4.py`), and the evaluation of all rows on explicit sets (`validate3.py`). `colgen.py JOB OUTPREFIX [ROUNDS]`
  takes the JSON text of a job. In each round it solves the linear program and adds the most violated Shannon rows
  over the closed sets of the configuration. After `ROUNDS` rounds, when the value stalls, or as soon as a file
  `OUTPREFIX.stop` exists, it extracts the exact certificate and writes it to `OUTPREFIX.json`. The certificate of
  Theorem 1.3 came from one run on the job `inputs/R7a.json`, which lists three variables `w`, `v`, `u` of law `μ`
  and 48 distinct forms, to which the ground forms built from the coordinates are added (see `Lattice2` in
  `eng2.py`), and switches on the rows of the partial symmetries and partial reflections (options `pmerge` and
  `xshare`). The command was

      FOCUS=6 SAVE=3 INIT_FROM=start.pkl python3 colgen.py "$(cat inputs/R7a.json)" OUTPREFIX 80

  on a 384-core machine. Here `start.pkl` holds the Shannon rows of two earlier, weaker certificates,
  `inputs/warm1.json` (λ < 1.4216) and `inputs/warm2.json` (λ < 1.4235), converted by `cert2descs.py` and
  concatenated, and `FOCUS=6` makes the program price first the rows that involve the coordinate `u`. The run was
  stopped by hand with the stop file after nine rounds (numbered 0 to 8), so a rerun would have to stop at the same
  point. We have not rerun it, so we do not claim that a rerun reproduces the certificate byte for byte.

## License

Code: Apache-2.0 (see `LICENSE`). Certificates and paper: CC BY 4.0. The files in `lean/SumDifference/` are
L. J. Kleinwaks' work under Apache-2.0 (`lean/third_party/kleinwaks_sum_difference/LICENSE`), as modified for
the port described in `lean/NOTICE`.
