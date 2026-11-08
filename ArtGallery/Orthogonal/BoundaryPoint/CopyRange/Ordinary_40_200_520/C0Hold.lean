module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520.C0Defs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520.C0S0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520.C0S1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520.C0S2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520.C0S3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520.C0S4
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520.C0S5
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520.C0S6

/-! Range data of profile `Ordinary_40_200_520`: `C0Hold` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.Ordinary_40_200_520
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

-- @@HOLD c0

/-- Closed forms of the registers of channel 0, step by step. -/
theorem c0hold {args xs : List ℚ} (m : Model args xs rows boxes cache) {x y z : ℝ}
    (hin : ∀ k Q d, (k,Q,d)∈c0ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev x y z Q)
    (B : PolyBox.Box (1/65:ℚ) (199/5005:ℚ) (797/18590:ℚ) x y z) :
    ∀ t∈c0tops, RegCert.Holds xs x y z t.1 t.2.1 t.2.2 := by
  have h1241 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1241
  have h1240 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1240
  have h1239 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1239
  have h1236 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1241]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1236
  have h1235 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1235
  have h1234 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1235]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1234
  have h1233 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1236,c0f1234]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1233
  have h1228 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1228
  have h1227 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1239,c0f1228]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1227
  have h1226 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1226
  have h1225 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1227,c0f1226]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1225
  have h1224 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1224
  have h1223 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1241,c0f1224]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1223
  have h1222 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1240,c0f1223]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1222
  have h1221 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1225,c0f1222]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1221
  have h1220 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1220
  have h1219 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1220]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1219
  have h1218 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1241,c0f1219]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1218
  have h1217 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1217
  have h1216 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1241,c0f1217]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1216
  have h1215 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1218]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1215
  have h1214 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1214
  have h1213 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1215,c0f1214]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1213
  have h1212 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1221]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1212
  have h1211 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1211
  have h1210 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1212,c0f1211]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1210
  have h1209 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1210]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1209
  have h1208 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1213,c0f1209]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1208
  have h1207 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1221,c0f1208]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1207
  have h1206 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1207]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1206
  have h1205 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1218,c0f1206]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1205
  have h1204 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1204
  have h1203 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1218,c0f1204]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1203
  have h1202 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1233,c0f1218]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1202
  have h1201 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1221,c0f1202]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1201
  have h1200 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1233,c0f1203]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1200
  have h1199 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1199
  have h1198 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1200,c0f1199]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1198
  have h1197 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1198]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1197
  have h1196 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1201,c0f1197]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1196
  have h1195 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1204,c0f1196]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1195
  have h1194 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1194
  have h1193 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1195,c0f1194]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1193
  have h1192 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1233,c0f1208]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1192
  have h1191 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1221,c0f1204]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1191
  have h1190 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1191]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1190
  have h1189 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1199,c0f1190]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1189
  have h1188 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1192,c0f1189]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1188
  have h1187 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1197,c0f1188]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1187
  have h1186 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1187]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1186
  have h1185 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1193,c0f1186]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1185
  have h1184 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1184
  have h1183 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1216,c0f1184]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1183
  have h1182 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1208,c0f1183]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1182
  have h1179 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1185,c0f1182]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1179
  have h1178 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1178
  have h1177 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1178]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1177
  have h1176 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1179,c0f1177]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1176
  have h1175 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1175
  have h1174 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1233,c0f1175]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1174
  have h1173 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1211,c0f1174]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1173
  have h1172 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1172
  have h1171 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1173,c0f1172]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1171
  have h1170 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1170
  have h1169 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1218,c0f1170]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1169
  have h1168 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1171,c0f1169]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1168
  have h1167 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1218,c0f1199]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1167
  have h1166 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1172,c0f1167]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1166
  have h1165 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1166]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1165
  have h1164 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1168,c0f1165]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1164
  have h1163 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1199,c0f1164]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1163
  have h1162 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1162
  have h1161 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1163,c0f1162]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1161
  have h1160 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1160
  have h1159 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1216,c0f1160]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1159
  have h1158 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1170,c0f1159]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1158
  have h1157 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1211]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1157
  have h1156 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1158,c0f1157]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1156
  have h1155 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1208,c0f1156]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1155
  have h1154 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1165,c0f1155]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1154
  have h1153 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1154]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1153
  have h1152 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1161,c0f1153]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1152
  have h1151 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1176]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1151
  have h1150 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1211]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1150
  have h1149 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1151,c0f1150]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1149
  have h1148 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1152,c0f1151]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1148
  have h1147 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1164]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1147
  have h1146 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1148,c0f1147]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1146
  have h1143 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1143
  have h1142 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1146,c0f1143]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1142
  have h1141 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1149,c0f1142]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1141
  have h1140 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1177,c0f1141]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1140
  have h1139 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1221,c0f1174]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1139
  have h1138 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1140,c0f1139]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1138
  have h1137 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1138]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1137
  have h1136 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1182,c0f1137]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1136
  have h1135 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1151,c0f1136]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1135
  have h1134 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1177,c0f1135]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1134
  have h1133 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1233,c0f1172]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1133
  have h1132 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1211,c0f1208]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1132
  have h1131 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1210,c0f1172]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1131
  have h1130 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1132,c0f1131]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1130
  have h1129 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1221,c0f1133]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1129
  have h1128 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1208,c0f1129]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1128
  have h1127 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1128]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1127
  have h1126 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1130,c0f1127]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1126
  have h1125 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1133]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1125
  have h1124 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1199,c0f1125]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1124
  have h1123 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1124]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1123
  have h1122 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1126,c0f1123]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1122
  have h1121 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1218,c0f1176]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1121
  have h1120 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1121]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1120
  have h1119 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1122,c0f1120]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1119
  have h1114 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1218,c0f1140]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1114
  have h1113 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1208,c0f1114]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1113
  have h1112 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1119]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1112
  have h1111 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1113,c0f1112]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1111
  have h1110 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1176,c0f1134]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1110
  have h1109 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1134,c0f1111]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1109
  have h1108 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1109]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1108
  have h1107 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1140,c0f1108]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1107
  have h1106 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1221,c0f1140]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1106
  have h1105 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1176,c0f1106]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1105
  have h1104 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1202,c0f1105]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1104
  have h1103 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1233,c0f1113]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1103
  have h1102 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1199,c0f1103]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1102
  have h1101 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1102]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1101
  have h1100 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1104,c0f1101]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1100
  have h1099 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1100]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1099
  have h1098 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1221,c0f1099]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1098
  have h1097 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1211,c0f1107]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1097
  have h1096 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1110,c0f1097]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1096
  have h1095 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1215,c0f1096]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1095
  have h1094 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1208,c0f1172]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1094
  have h1093 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1218,c0f1107]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1093
  have h1092 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1094,c0f1093]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1092
  have h1091 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1092]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1091
  have h1090 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1095,c0f1091]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1090
  have h1089 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1211,c0f1090]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1089
  have h1088 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1208,c0f1133]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1088
  have h1087 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1172,c0f1088]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1087
  have h1086 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1210,c0f1087]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1086
  have h1085 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1123,c0f1086]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1085
  have h1084 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1211,c0f1140]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1084
  have h1083 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1176,c0f1084]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1083
  have h1082 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1218,c0f1083]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1082
  have h1081 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1082]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1081
  have h1080 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1085,c0f1081]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1080
  have h1079 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1113,c0f1090]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1079
  have h1078 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1079]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1078
  have h1077 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1080,c0f1078]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1077
  have h1076 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1112,c0f1077]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1076
  have h1075 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1134,c0f1076]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1075
  have h1074 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1098]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1074
  have h1073 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1089,c0f1074]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1073
  have h1072 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1073]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1072
  have h1071 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1075,c0f1072]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1071
  have h1070 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1070
  have h1069 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1233,c0f1070]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1069
  have h1068 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1101,c0f1069]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1068
  have h1067 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1091,c0f1069]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1067
  have h1066 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1089,c0f1067]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1066
  have h1062 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1076,c0f1068]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1062
  have h1061 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1111,c0f1098]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1061
  have h1060 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1061]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1060
  have h1059 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1199,c0f1060]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1059
  have h1058 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1067,c0f1059]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1058
  have h1057 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1058]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1057
  have h1056 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1062,c0f1057]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1056
  have h1055 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1134,c0f1056]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1055
  have h1054 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1074,c0f1066]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1054
  have h1053 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1068]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1053
  have h1052 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1054,c0f1053]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1052
  have h1051 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1073,c0f1052]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1051
  have h1050 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1051]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1050
  have h1049 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1055,c0f1050]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1049
  have h1047 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1233,c0f1160]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1047
  have h1046 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1091,c0f1047]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1046
  have h1045 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1089,c0f1046]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1045
  have h1043 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1059,c0f1046]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1043
  have h1042 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1043]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1042
  have h1041 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1062,c0f1042]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1041
  have h1040 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1134,c0f1041]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1040
  have h1039 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1074,c0f1045]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1039
  have h1038 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1053,c0f1039]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1038
  have h1037 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1073,c0f1038]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1037
  have h1036 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1037]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1036
  have h1035 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1040,c0f1036]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1035
  have h1033 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1174,c0f1101]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1033
  have h1029 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1076,c0f1033]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1029
  have h1028 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1057,c0f1029]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1028
  have h1027 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1134,c0f1028]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1027
  have h1026 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1033]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1026
  have h1025 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1054,c0f1026]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1025
  have h1024 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1073,c0f1025]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1024
  have h1023 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1024]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1023
  have h1022 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1027,c0f1023]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1022
  have h1019 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1042,c0f1029]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1019
  have h1018 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1134,c0f1019]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1018
  have h1017 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1039,c0f1026]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1017
  have h1016 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1073,c0f1017]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1016
  have h1015 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1016]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1015
  have h1014 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1018,c0f1015]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1014
  have h1012 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1049]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1012
  have h1011 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1035]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1011
  have h1010 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1022]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1010
  have h1009 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1014]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1009
  have h1008 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1012,c0f1011]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1008
  have h1007 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1010,c0f1008]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1007
  have h1006 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1009,c0f1007]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k1006
  have h1005 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1006]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k1005
  have h1003 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k1003
  have h969 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1205,c0f1121]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k969
  have h968 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1208,c0f1199]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k968
  have h967 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1093,c0f968]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k967
  have h966 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1140,c0f1071]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k966
  have h965 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1218,c0f966]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k965
  have h964 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f968,c0f965]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k964
  have h506 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1114,c0f968]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k506
  have h483 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k483
  have h482 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f483]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k482
  have h481 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1233,c0f482]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k481
  have h478 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k478
  have h477 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f478]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k477
  have h476 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1218,c0f477]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k476
  have h456 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1218,c0f1110]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k456
  have h455 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1205,c0f456]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k455
  have h454 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1071,c0f1003]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k454
  have h453 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1005,c0f454]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k453
  have h452 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1177,c0f453]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k452
  have h451 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1140,c0f452]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k451
  have h450 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f1218,c0f451]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k450
  have h449 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f968,c0f450]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k449
  have h174 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f482,c0f476]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k174
  have h173 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f174]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k173
  have h172 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k172
  have h171 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f173,c0f172]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k171
  have h170 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f171]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k170
  have h169 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c0k169
  have h168 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f169]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k168
  have h167 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f476,c0f168]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k167
  have h166 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f167]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k166
  have h165 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f969,c0f166]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k165
  have h162 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f170,c0f165]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k162
  have h154 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f165]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c0k154
  have h150 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f162,c0f154]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k150
  have h149 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f481,c0f150]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k149
  have h148 := RegChain.out_sound m.run m.bounds hin B (known:=[c0f165,c0f149]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c0k148
  intro t ht
  simp only [c0tops,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> assumption

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520
end
