module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2Defs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S4
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S5
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S6

/-! Range data of profile `Lower_10_40_1000`: `C2Hold` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.Lower_10_40_1000
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

-- @@HOLD c2

/-- Closed forms of the registers of channel 2, step by step. -/
theorem c2hold {args xs : List ℚ} (m : Model args xs rows boxes cache) {x y z : ℝ}
    (hin : ∀ k Q d, (k,Q,d)∈c2ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev x y z Q)
    (B : PolyBox.Box (1/65:ℚ) (4999/5005:ℚ) (130379/130130:ℚ) x y z) :
    ∀ t∈c2tops, RegCert.Holds xs x y z t.1 t.2.1 t.2.2 := by
  have h1239 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1239
  have h1238 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1238
  have h1235 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1235
  have h1234 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1239]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k1234
  have h1233 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1233
  have h1232 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1233]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k1232
  have h1231 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1234,c2f1232]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1231
  have h1230 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1230
  have h1229 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1231,c2f1230]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1229
  have h1228 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1228
  have h1227 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1229,c2f1228]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1227
  have h1226 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1226
  have h1222 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1222
  have h1221 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1239,c2f1222]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1221
  have h1220 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1238,c2f1221]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1220
  have h1218 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1218
  have h1217 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1218]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k1217
  have h1216 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1239,c2f1217]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1216
  have h1215 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1215
  have h1214 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1239,c2f1215]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1214
  have h1213 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1216]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k1213
  have h1212 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1212
  have h1211 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1213,c2f1212]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1211
  have h1202 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1202
  have h1201 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1216,c2f1202]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1201
  have h1200 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1231,c2f1216]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1200
  have h1198 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1231,c2f1201]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1198
  have h1197 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1197
  have h1196 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1198,c2f1197]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1196
  have h1195 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1196]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k1195
  have h1192 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1192
  have h1182 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1182
  have h1181 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1214,c2f1182]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1181
  have h1176 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1176
  have h1175 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1176]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k1175
  have h1170 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1170
  have h1169 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1216,c2f1170]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1169
  have h1167 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1216,c2f1197]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1167
  have h1162 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1162
  have h1143 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1143
  have h1070 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k1070
  have h1069 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1231,c2f1070]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k1069
  have h996 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1230,c2f1216]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k996
  have h995 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1231,c2f996]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k995
  have h993 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1231]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k993
  have h992 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1197,c2f993]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k992
  have h991 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f992]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k991
  have h743 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1235,c2f1226]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k743
  have h742 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k742
  have h741 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f743,c2f742]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k741
  have h740 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1220,c2f741]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k740
  have h739 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f740]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k739
  have h738 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1227,c2f739]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k738
  have h737 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f738]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k737
  have h736 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1211,c2f737]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k736
  have h735 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f740,c2f736]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k735
  have h734 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f735]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k734
  have h733 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1216,c2f734]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k733
  have h732 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1200,c2f740]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k732
  have h731 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1195,c2f732]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k731
  have h730 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1202,c2f731]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k730
  have h729 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1192,c2f730]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k729
  have h728 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1231,c2f736]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k728
  have h727 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1202,c2f740]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k727
  have h726 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f727]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k726
  have h725 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1197,c2f726]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k725
  have h724 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f728,c2f725]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k724
  have h723 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1195,c2f724]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k723
  have h722 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f723]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k722
  have h721 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f729,c2f722]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k721
  have h720 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1181,c2f736]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k720
  have h717 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f721,c2f720]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k717
  have h716 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1175,c2f717]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k716
  have h715 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1229,c2f1227]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k715
  have h714 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k714
  have h713 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f715,c2f714]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k713
  have h712 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1169,c2f713]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k712
  have h711 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1167,c2f714]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k711
  have h710 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f711]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k710
  have h709 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f712,c2f710]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k709
  have h708 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1197,c2f709]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k708
  have h707 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1162,c2f708]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k707
  have h706 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k706
  have h705 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1214,c2f706]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k705
  have h704 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1170,c2f705]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k704
  have h703 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1227,c2f1197]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k703
  have h702 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f703]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k702
  have h701 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f704,c2f702]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k701
  have h700 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f736,c2f701]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k700
  have h699 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f710,c2f700]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k699
  have h698 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f699]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k698
  have h697 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f707,c2f698]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k697
  have h696 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f716]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k696
  have h695 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1227]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k695
  have h694 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f696,c2f695]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k694
  have h693 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f697,c2f696]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k693
  have h692 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f709]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k692
  have h691 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f693,c2f692]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k691
  have h688 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1143,c2f691]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k688
  have h687 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f694,c2f688]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k687
  have h686 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1175,c2f687]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k686
  have h685 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1229,c2f740]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k685
  have h684 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f686,c2f685]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k684
  have h683 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f684]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k683
  have h682 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f720,c2f683]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k682
  have h681 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f696,c2f682]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k681
  have h680 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1175,c2f681]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k680
  have h679 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1231,c2f714]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k679
  have h678 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1227,c2f736]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k678
  have h677 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f738,c2f714]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k677
  have h676 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f678,c2f677]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k676
  have h675 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f740,c2f679]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k675
  have h674 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f736,c2f675]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k674
  have h673 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f674]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k673
  have h672 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f676,c2f673]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k672
  have h671 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f679]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k671
  have h670 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1197,c2f671]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k670
  have h669 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f670]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k669
  have h668 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f672,c2f669]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k668
  have h667 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1216,c2f716]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k667
  have h666 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f667]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k666
  have h665 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f668,c2f666]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k665
  have h660 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1216,c2f686]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k660
  have h659 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f736,c2f660]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k659
  have h658 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f665]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k658
  have h657 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f659,c2f658]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k657
  have h656 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f716,c2f680]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k656
  have h655 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f680,c2f657]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k655
  have h654 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f655]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k654
  have h653 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f686,c2f654]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k653
  have h652 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f740,c2f686]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k652
  have h651 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f716,c2f652]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k651
  have h650 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1200,c2f651]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k650
  have h649 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1231,c2f659]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k649
  have h648 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1197,c2f649]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k648
  have h647 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f648]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k647
  have h646 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f650,c2f647]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k646
  have h645 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f646]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k645
  have h644 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f740,c2f645]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k644
  have h643 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1227,c2f653]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k643
  have h642 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f656,c2f643]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k642
  have h641 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1213,c2f642]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k641
  have h640 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f736,c2f714]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k640
  have h639 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1216,c2f653]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k639
  have h638 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f640,c2f639]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k638
  have h637 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f638]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k637
  have h636 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f641,c2f637]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k636
  have h635 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1227,c2f636]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k635
  have h634 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f736,c2f679]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k634
  have h633 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f714,c2f634]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k633
  have h632 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f738,c2f633]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k632
  have h631 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f669,c2f632]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k631
  have h630 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1227,c2f686]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k630
  have h629 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f716,c2f630]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k629
  have h628 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1216,c2f629]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k628
  have h627 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f628]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k627
  have h626 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f631,c2f627]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k626
  have h625 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f659,c2f636]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k625
  have h624 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f625]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k624
  have h623 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f626,c2f624]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k623
  have h622 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f658,c2f623]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k622
  have h621 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f680,c2f622]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k621
  have h620 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f644]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k620
  have h619 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f635,c2f620]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k619
  have h618 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f619]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k618
  have h617 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f621,c2f618]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k617
  have h616 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1069,c2f647]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k616
  have h615 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1069,c2f637]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k615
  have h614 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f635,c2f615]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k614
  have h613 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f644,c2f616]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k613
  have h610 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f622,c2f616]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k610
  have h609 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f657,c2f644]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k609
  have h608 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f609]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k608
  have h607 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1197,c2f608]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k607
  have h606 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f615,c2f607]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k606
  have h605 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f606]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k605
  have h604 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f610,c2f605]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k604
  have h603 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f680,c2f604]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k603
  have h602 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f620,c2f614]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k602
  have h601 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f616]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k601
  have h600 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f602,c2f601]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k600
  have h599 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f619,c2f600]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k599
  have h598 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f599]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k598
  have h597 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f603,c2f598]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k597
  have h596 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f617,c2f597]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k596
  have h595 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1231,c2f706]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k595
  have h594 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f637,c2f595]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k594
  have h593 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f635,c2f594]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k593
  have h591 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f607,c2f594]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k591
  have h590 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f591]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k590
  have h589 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f610,c2f590]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k589
  have h588 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f680,c2f589]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k588
  have h587 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f620,c2f593]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k587
  have h586 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f601,c2f587]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k586
  have h585 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f619,c2f586]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k585
  have h584 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f585]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k584
  have h583 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f588,c2f584]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k583
  have h582 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f617,c2f583]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k582
  have h581 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1229,c2f647]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k581
  have h580 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f644,c2f581]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k580
  have h577 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f622,c2f581]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k577
  have h576 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f605,c2f577]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k576
  have h575 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f680,c2f576]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k575
  have h574 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f581]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k574
  have h573 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f602,c2f574]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k573
  have h572 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f619,c2f573]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k572
  have h571 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f572]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k571
  have h570 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f575,c2f571]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k570
  have h569 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f617,c2f570]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k569
  have h567 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f590,c2f577]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k567
  have h566 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f680,c2f567]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k566
  have h565 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f587,c2f574]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k565
  have h564 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f619,c2f565]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k564
  have h563 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f564]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k563
  have h562 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f566,c2f563]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k562
  have h561 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f617,c2f562]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k561
  have h542 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f995,c2f740]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k542
  have h541 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f991,c2f542]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k541
  have h540 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f655,c2f617]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k540
  have h539 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f541,c2f540]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k539
  have h538 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f539]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k538
  have h525 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1197,c2f736]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k525
  have h446 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c2k446
  have h411 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f613,c2f596]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k411
  have h410 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f411]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k410
  have h409 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f716,c2f410]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k409
  have h408 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f613,c2f582]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k408
  have h407 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f408]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k407
  have h406 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f716,c2f407]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k406
  have h405 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f580,c2f569]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k405
  have h404 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f405]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k404
  have h403 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f716,c2f404]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k403
  have h402 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f580,c2f561]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k402
  have h401 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f402]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k401
  have h400 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f716,c2f401]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k400
  have h399 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f409,c2f406]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k399
  have h398 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f403,c2f399]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k398
  have h397 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f400,c2f398]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k397
  have h396 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f656,c2f538]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k396
  have h395 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f660,c2f525]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k395
  have h394 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1216,c2f656]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k394
  have h393 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f733,c2f394]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k393
  have h386 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f397]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k386
  have h385 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f396,c2f386]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k385
  have h384 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f446,c2f385]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k384
  have h383 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f397,c2f384]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k383
  have h382 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1216,c2f383]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k382
  have h381 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f733,c2f382]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k381
  have h349 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f714]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k349
  have h348 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1216,c2f349]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k348
  have h221 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f525,c2f395]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k221
  have h220 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1175,c2f221]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k220
  have h196 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f381]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c2k196
  have h195 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f393,c2f196]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k195
  have h192 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f1175,c2f195]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k192
  have h191 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f393,c2f192]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k191
  have h35 := RegChain.out_sound m.run m.bounds hin B (known:=[c2f733,c2f348]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c2k35
  intro t ht
  simp only [c2tops,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000
end
