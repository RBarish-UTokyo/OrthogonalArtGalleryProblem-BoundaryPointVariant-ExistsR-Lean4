module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1XDefs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1S0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1S1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1S2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1S3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1S4
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1S5
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1S6
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1XS0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1XS1

/-! Range data of profile `Shifted_40_200_520`: `C1XHold` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.Shifted_40_200_520
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

-- @@HOLD c1

noncomputable def c1xtops : List (Nat × Ex × Ex) := [c1f1213,c1f1198,c1f748,c1f744,c1f424,c1f268,c1f239,c1f77]

/-- Closed forms of the registers of the other test of channel 1, step by step. -/
theorem c1xhold {args xs : List ℚ} (m : Model args xs rows boxes cache) {x y z : ℝ}
    (hin : ∀ k Q d, (k,Q,d)∈c1ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev x y z Q)
    (B : PolyBox.Box (1/65:ℚ) (999/5005:ℚ) (26379/130130:ℚ) x y z) :
    ∀ t∈c1xtops, RegCert.Holds xs x y z t.1 t.2.1 t.2.2 := by
  have h1240 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1240
  have h1239 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1239
  have h1237 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1237
  have h1235 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1240]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k1235
  have h1234 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1234
  have h1233 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1234]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k1233
  have h1232 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1235,c1f1233]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1232
  have h1231 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1231
  have h1227 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1227
  have h1223 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1223
  have h1222 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1240,c1f1223]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1222
  have h1221 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1239,c1f1222]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1221
  have h1219 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1219
  have h1218 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1219]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k1218
  have h1217 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1240,c1f1218]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1217
  have h1216 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1216
  have h1215 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1240,c1f1216]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1215
  have h1214 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k1214
  have h1213 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1213
  have h1212 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1214,c1f1213]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1212
  have h1203 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1203
  have h1202 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217,c1f1203]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1202
  have h1201 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1232,c1f1217]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1201
  have h1199 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1232,c1f1202]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1199
  have h1198 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1198
  have h1197 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1199,c1f1198]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1197
  have h1196 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1197]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k1196
  have h1193 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1193
  have h1183 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1183
  have h1182 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1215,c1f1183]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1182
  have h1177 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1231]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k1177
  have h1175 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1175
  have h1174 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1232,c1f1175]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1174
  have h1170 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1170
  have h1169 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217,c1f1170]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1169
  have h1167 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217,c1f1198]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1167
  have h1162 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1162
  have h1143 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1143
  have h1070 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1070
  have h1069 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1232,c1f1070]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1069
  have h996 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217,c1f1175]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k996
  have h995 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1232,c1f996]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k995
  have h993 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1232]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k993
  have h992 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1198,c1f993]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k992
  have h991 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f992]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k991
  have h963 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1237,c1f1227]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k963
  have h962 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k962
  have h961 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f963,c1f962]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k961
  have h960 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1221,c1f961]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k960
  have h959 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f960]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k959
  have h958 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k958
  have h957 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f959,c1f958]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k957
  have h956 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f957]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k956
  have h955 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1212,c1f956]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k955
  have h954 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f960,c1f955]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k954
  have h953 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f954]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k953
  have h952 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217,c1f953]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k952
  have h951 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1201,c1f960]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k951
  have h950 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1196,c1f951]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k950
  have h949 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1203,c1f950]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k949
  have h948 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1193,c1f949]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k948
  have h947 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1232,c1f955]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k947
  have h946 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1203,c1f960]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k946
  have h945 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f946]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k945
  have h944 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1198,c1f945]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k944
  have h943 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f947,c1f944]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k943
  have h942 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1196,c1f943]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k942
  have h941 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f942]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k941
  have h940 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f948,c1f941]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k940
  have h939 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1182,c1f955]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k939
  have h936 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f940,c1f939]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k936
  have h935 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1177,c1f936]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k935
  have h934 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1174,c1f958]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k934
  have h933 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k933
  have h932 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f934,c1f933]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k932
  have h931 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1169,c1f932]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k931
  have h930 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1167,c1f933]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k930
  have h929 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f930]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k929
  have h928 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f931,c1f929]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k928
  have h927 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1198,c1f928]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k927
  have h926 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1162,c1f927]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k926
  have h925 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k925
  have h924 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1215,c1f925]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k924
  have h923 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1170,c1f924]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k923
  have h922 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f958]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k922
  have h921 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f923,c1f922]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k921
  have h920 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f955,c1f921]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k920
  have h919 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f929,c1f920]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k919
  have h918 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f919]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k918
  have h917 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f926,c1f918]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k917
  have h916 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f935]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k916
  have h915 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f958]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k915
  have h914 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f916,c1f915]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k914
  have h913 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f917,c1f916]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k913
  have h912 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f928]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k912
  have h911 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f913,c1f912]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k911
  have h908 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1143,c1f911]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k908
  have h907 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f914,c1f908]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k907
  have h906 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1177,c1f907]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k906
  have h905 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1174,c1f960]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k905
  have h904 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f906,c1f905]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k904
  have h903 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f904]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k903
  have h902 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f939,c1f903]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k902
  have h901 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f916,c1f902]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k901
  have h900 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1177,c1f901]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k900
  have h899 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1232,c1f933]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k899
  have h898 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f958,c1f955]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k898
  have h897 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f957,c1f933]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k897
  have h896 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f898,c1f897]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k896
  have h895 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f960,c1f899]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k895
  have h894 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f955,c1f895]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k894
  have h893 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f894]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k893
  have h892 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f896,c1f893]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k892
  have h891 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f899]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k891
  have h890 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1198,c1f891]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k890
  have h889 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f890]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k889
  have h888 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f892,c1f889]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k888
  have h887 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217,c1f935]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k887
  have h886 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f887]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k886
  have h885 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f888,c1f886]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k885
  have h880 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217,c1f906]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k880
  have h879 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f955,c1f880]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k879
  have h878 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f885]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k878
  have h877 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f879,c1f878]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k877
  have h876 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f935,c1f900]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k876
  have h875 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f900,c1f877]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k875
  have h874 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f875]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k874
  have h873 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f906,c1f874]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k873
  have h872 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f960,c1f906]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k872
  have h871 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f935,c1f872]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k871
  have h870 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1201,c1f871]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k870
  have h869 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1232,c1f879]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k869
  have h868 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1198,c1f869]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k868
  have h867 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f868]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k867
  have h866 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f870,c1f867]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k866
  have h865 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f866]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k865
  have h864 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f960,c1f865]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k864
  have h863 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f958,c1f873]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k863
  have h862 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f876,c1f863]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k862
  have h861 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1214,c1f862]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k861
  have h860 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f955,c1f933]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k860
  have h859 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217,c1f873]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k859
  have h858 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f860,c1f859]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k858
  have h857 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f858]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k857
  have h856 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f861,c1f857]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k856
  have h855 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f958,c1f856]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k855
  have h854 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f955,c1f899]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k854
  have h853 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f933,c1f854]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k853
  have h852 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f957,c1f853]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k852
  have h851 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f889,c1f852]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k851
  have h850 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f958,c1f906]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k850
  have h849 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f935,c1f850]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k849
  have h848 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217,c1f849]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k848
  have h847 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f848]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k847
  have h846 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f851,c1f847]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k846
  have h845 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f879,c1f856]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k845
  have h844 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f845]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k844
  have h843 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f846,c1f844]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k843
  have h842 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f878,c1f843]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k842
  have h841 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f900,c1f842]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k841
  have h840 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f864]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k840
  have h839 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f855,c1f840]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k839
  have h838 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f839]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k838
  have h837 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f841,c1f838]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k837
  have h836 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1069,c1f867]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k836
  have h835 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1069,c1f857]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k835
  have h834 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f855,c1f835]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k834
  have h833 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f864,c1f836]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k833
  have h830 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f842,c1f836]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k830
  have h829 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f877,c1f864]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k829
  have h828 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f829]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k828
  have h827 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1198,c1f828]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k827
  have h826 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f835,c1f827]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k826
  have h825 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f826]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k825
  have h824 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f825]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k824
  have h823 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f900,c1f824]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k823
  have h822 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f840,c1f834]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k822
  have h821 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f836]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k821
  have h820 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f822,c1f821]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k820
  have h819 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f839,c1f820]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k819
  have h818 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f819]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k818
  have h817 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f823,c1f818]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k817
  have h816 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f837,c1f817]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k816
  have h815 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1232,c1f925]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k815
  have h814 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f857,c1f815]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k814
  have h813 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f855,c1f814]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k813
  have h811 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f827,c1f814]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k811
  have h810 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f811]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k810
  have h809 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f810]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k809
  have h808 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f900,c1f809]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k808
  have h807 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f840,c1f813]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k807
  have h806 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f821,c1f807]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k806
  have h805 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f839,c1f806]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k805
  have h804 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f805]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k804
  have h803 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f808,c1f804]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k803
  have h802 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f837,c1f803]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k802
  have h801 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1174,c1f867]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k801
  have h800 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f864,c1f801]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k800
  have h797 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f842,c1f801]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k797
  have h796 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f825,c1f797]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k796
  have h795 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f900,c1f796]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k795
  have h794 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f801]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k794
  have h793 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f822,c1f794]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k793
  have h792 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f839,c1f793]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k792
  have h791 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f792]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k791
  have h790 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f795,c1f791]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k790
  have h789 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f837,c1f790]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k789
  have h787 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f810,c1f797]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k787
  have h786 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f900,c1f787]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k786
  have h785 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f807,c1f794]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k785
  have h784 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f839,c1f785]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k784
  have h783 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f784]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k783
  have h782 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f786,c1f783]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k782
  have h781 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f837,c1f782]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k781
  have h765 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f995,c1f960]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k765
  have h764 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f991,c1f765]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k764
  have h763 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f875,c1f837]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k763
  have h762 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f764,c1f763]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k762
  have h761 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f762]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k761
  have h748 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1198,c1f955]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k748
  have h746 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f906,c1f837]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k746
  have h745 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217,c1f746]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k745
  have h744 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f748,c1f745]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k744
  have h714 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k714
  have h493 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f880,c1f748]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k493
  have h446 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k446
  have h441 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f833,c1f816]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k441
  have h440 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f441]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k440
  have h439 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f935,c1f440]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k439
  have h438 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f833,c1f802]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k438
  have h437 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f438]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k437
  have h436 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f935,c1f437]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k436
  have h435 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f800,c1f789]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k435
  have h434 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f435]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k434
  have h433 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f935,c1f434]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k433
  have h432 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f800,c1f781]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k432
  have h431 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f432]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k431
  have h430 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f935,c1f431]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k430
  have h429 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f439,c1f436]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k429
  have h428 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f433,c1f429]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k428
  have h427 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f430,c1f428]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k427
  have h426 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f876,c1f761]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k426
  have h425 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217,c1f876]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k425
  have h424 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f952,c1f425]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k424
  have h417 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f427]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k417
  have h416 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f426,c1f417]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k416
  have h415 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f446,c1f416]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k415
  have h414 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f427,c1f415]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k414
  have h413 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217,c1f414]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k413
  have h412 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f952,c1f413]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k412
  have h349 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f714]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k349
  have h348 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1217,c1f349]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k348
  have h269 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f748,c1f493]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k269
  have h268 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1177,c1f269]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k268
  have h244 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f412]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k244
  have h243 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f424,c1f244]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k243
  have h240 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1177,c1f243]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k240
  have h239 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f424,c1f240]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k239
  have h77 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f952,c1f348]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k77
  intro t ht
  simp only [c1xtops,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> assumption

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520
end
