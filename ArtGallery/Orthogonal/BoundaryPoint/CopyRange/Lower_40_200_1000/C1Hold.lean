module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000.C1Defs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000.C1S0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000.C1S1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000.C1S2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000.C1S3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000.C1S4
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000.C1S5
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000.C1S6

/-! Range data of profile `Lower_40_200_1000`: `C1Hold` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.Lower_40_200_1000
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

-- @@HOLD c1

/-- Closed forms of the registers of channel 1, step by step. -/
theorem c1hold {args xs : List ℚ} (m : Model args xs rows boxes cache) {x y z : ℝ}
    (hin : ∀ k Q d, (k,Q,d)∈c1ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev x y z Q)
    (B : PolyBox.Box (1/65:ℚ) (999/5005:ℚ) (26379/130130:ℚ) x y z) :
    ∀ t∈c1tops, RegCert.Holds xs x y z t.1 t.2.1 t.2.2 := by
  have h1239 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1239
  have h1238 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1238
  have h1236 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1236
  have h1234 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1239]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k1234
  have h1233 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1233
  have h1232 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1233]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k1232
  have h1231 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1234,c1f1232]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1231
  have h1230 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1230
  have h1229 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1231,c1f1230]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1229
  have h1226 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1226
  have h1222 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1222
  have h1221 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1239,c1f1222]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1221
  have h1220 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1238,c1f1221]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1220
  have h1218 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1218
  have h1217 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1218]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k1217
  have h1216 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1239,c1f1217]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1216
  have h1215 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1215
  have h1214 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1239,c1f1215]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1214
  have h1213 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k1213
  have h1212 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1212
  have h1211 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1213,c1f1212]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1211
  have h1202 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1202
  have h1201 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216,c1f1202]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1201
  have h1200 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1231,c1f1216]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1200
  have h1198 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1231,c1f1201]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1198
  have h1197 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1197
  have h1196 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1198,c1f1197]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1196
  have h1195 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1196]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k1195
  have h1192 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1192
  have h1182 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1182
  have h1181 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1214,c1f1182]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1181
  have h1176 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1176
  have h1175 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1176]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k1175
  have h1170 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1170
  have h1169 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216,c1f1170]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1169
  have h1167 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216,c1f1197]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1167
  have h1162 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1162
  have h1143 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1143
  have h1070 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k1070
  have h1069 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1231,c1f1070]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k1069
  have h963 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1236,c1f1226]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k963
  have h962 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k962
  have h961 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f963,c1f962]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k961
  have h960 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1220,c1f961]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k960
  have h959 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f960]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k959
  have h958 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k958
  have h957 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f959,c1f958]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k957
  have h956 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f957]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k956
  have h955 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1211,c1f956]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k955
  have h954 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f960,c1f955]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k954
  have h953 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f954]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k953
  have h952 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216,c1f953]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k952
  have h951 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1200,c1f960]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k951
  have h950 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1195,c1f951]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k950
  have h949 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1202,c1f950]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k949
  have h948 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1192,c1f949]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k948
  have h947 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1231,c1f955]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k947
  have h946 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1202,c1f960]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k946
  have h945 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f946]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k945
  have h944 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1197,c1f945]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k944
  have h943 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f947,c1f944]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k943
  have h942 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1195,c1f943]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k942
  have h941 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f942]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k941
  have h940 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f948,c1f941]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k940
  have h939 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1181,c1f955]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k939
  have h936 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f940,c1f939]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k936
  have h935 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1175,c1f936]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k935
  have h934 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1229,c1f958]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k934
  have h933 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k933
  have h932 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f934,c1f933]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k932
  have h931 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1169,c1f932]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k931
  have h930 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1167,c1f933]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k930
  have h929 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f930]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k929
  have h928 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f931,c1f929]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k928
  have h927 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1197,c1f928]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k927
  have h926 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1162,c1f927]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k926
  have h925 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k925
  have h924 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1214,c1f925]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k924
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
  have h906 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1175,c1f907]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k906
  have h905 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1229,c1f960]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k905
  have h904 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f906,c1f905]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k904
  have h903 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f904]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k903
  have h902 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f939,c1f903]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k902
  have h901 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f916,c1f902]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k901
  have h900 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1175,c1f901]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k900
  have h899 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1231,c1f933]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k899
  have h898 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f958,c1f955]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k898
  have h897 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f957,c1f933]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k897
  have h896 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f898,c1f897]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k896
  have h895 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f960,c1f899]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k895
  have h894 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f955,c1f895]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k894
  have h893 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f894]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k893
  have h892 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f896,c1f893]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k892
  have h891 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f899]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k891
  have h890 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1197,c1f891]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k890
  have h889 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f890]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k889
  have h888 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f892,c1f889]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k888
  have h887 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216,c1f935]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k887
  have h886 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f887]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k886
  have h885 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f888,c1f886]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k885
  have h880 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216,c1f906]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k880
  have h879 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f955,c1f880]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k879
  have h878 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f885]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k878
  have h877 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f879,c1f878]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k877
  have h876 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f935,c1f900]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k876
  have h875 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f900,c1f877]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k875
  have h874 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f875]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k874
  have h873 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f906,c1f874]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k873
  have h872 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f960,c1f906]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k872
  have h871 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f935,c1f872]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k871
  have h870 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1200,c1f871]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k870
  have h869 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1231,c1f879]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k869
  have h868 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1197,c1f869]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k868
  have h867 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f868]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k867
  have h866 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f870,c1f867]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k866
  have h865 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f866]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k865
  have h864 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f960,c1f865]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k864
  have h863 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f958,c1f873]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k863
  have h862 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f876,c1f863]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k862
  have h861 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1213,c1f862]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k861
  have h860 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f955,c1f933]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k860
  have h859 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216,c1f873]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k859
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
  have h848 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216,c1f849]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k848
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
  have h830 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f842,c1f836]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k830
  have h829 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f877,c1f864]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k829
  have h828 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f829]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k828
  have h827 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1197,c1f828]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k827
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
  have h815 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1231,c1f925]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k815
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
  have h801 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1229,c1f867]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k801
  have h797 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f842,c1f801]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k797
  have h796 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f825,c1f797]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k796
  have h795 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f900,c1f796]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k795
  have h794 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f801]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k794
  have h793 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f822,c1f794]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k793
  have h792 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f839,c1f793]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k792
  have h791 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f792]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k791
  have h790 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f795,c1f791]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k790
  have h787 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f810,c1f797]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k787
  have h786 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f900,c1f787]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k786
  have h785 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f807,c1f794]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k785
  have h784 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f839,c1f785]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k784
  have h783 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f784]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k783
  have h782 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f786,c1f783]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k782
  have h780 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f817]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k780
  have h779 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f803]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k779
  have h778 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f790]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k778
  have h777 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f782]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k777
  have h776 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f780,c1f779]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k776
  have h775 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f778,c1f776]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k775
  have h774 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f777,c1f775]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k774
  have h773 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f774]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k773
  have h771 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k771
  have h749 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f952,c1f887]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k749
  have h748 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1197,c1f955]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k748
  have h747 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f859,c1f748]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k747
  have h746 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f906,c1f837]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k746
  have h745 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216,c1f746]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k745
  have h744 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f748,c1f745]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k744
  have h551 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k551
  have h493 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f880,c1f748]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k493
  have h483 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k483
  have h482 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f483]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k482
  have h481 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1231,c1f482]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k481
  have h478 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k478
  have h477 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f478]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k477
  have h476 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216,c1f477]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k476
  have h425 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216,c1f876]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k425
  have h424 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f952,c1f425]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k424
  have h423 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f837,c1f771]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k423
  have h422 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f773,c1f423]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k422
  have h421 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1175,c1f422]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k421
  have h420 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f906,c1f421]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k420
  have h419 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216,c1f420]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k419
  have h418 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f748,c1f419]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k418
  have h340 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f551]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k340
  have h339 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f1216,c1f340]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k339
  have h338 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f339]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k338
  have h332 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f749,c1f338]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k332
  have h174 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f482,c1f476]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k174
  have h173 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f174]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k173
  have h172 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k172
  have h171 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f173,c1f172]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k171
  have h170 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f171]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k170
  have h169 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k169
  have h168 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f169]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k168
  have h167 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f476,c1f168]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k167
  have h166 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f167]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k166
  have h164 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f170]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k164
  have h140 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f749,c1f166]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k140
  have h139 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f164,c1f140]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k139
  have h135 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f140]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k135
  have h134 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f139,c1f135]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k134
  have h133 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f481,c1f134]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k133
  have h132 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f140,c1f133]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k132
  intro t ht
  simp only [c1tops,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> assumption

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000
end
