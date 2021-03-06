/* Generated by Nimrod Compiler v0.8.9 */
/*   (c) 2010 Andreas Rumpf */

typedef long long int NI;
typedef unsigned long long int NU;
#include "nimbase.h"

typedef struct TY50525 TY50525;
typedef struct TY42532 TY42532;
typedef struct NimStringDesc NimStringDesc;
typedef struct TGenericSeq TGenericSeq;
typedef struct TY50551 TY50551;
typedef struct TY50547 TY50547;
typedef struct TY49011 TY49011;
typedef struct TY50519 TY50519;
typedef struct TY70013 TY70013;
typedef struct TY49005 TY49005;
typedef struct TNimObject TNimObject;
typedef struct TNimType TNimType;
typedef struct TNimNode TNimNode;
typedef struct TY50549 TY50549;
typedef struct TY50539 TY50539;
typedef struct TY47008 TY47008;
typedef struct TY50529 TY50529;
typedef struct TY50527 TY50527;
typedef struct TY50543 TY50543;
typedef struct TY38013 TY38013;
struct TY42532 {
NI16 Line;
NI16 Col;
NI32 Fileindex;
};
struct TGenericSeq {
NI len;
NI space;
};
typedef NIM_CHAR TY239[100000001];
struct NimStringDesc {
  TGenericSeq Sup;
TY239 data;
};
struct TY50525 {
TY50551* Typ;
NimStringDesc* Comment;
TY42532 Info;
NU8 Flags;
NU8 Kind;
union {
struct {NI64 Intval;
} S1;
struct {NF64 Floatval;
} S2;
struct {NimStringDesc* Strval;
} S3;
struct {TY50547* Sym;
} S4;
struct {TY49011* Ident;
} S5;
struct {TY50519* Sons;
} S6;
} KindU;
};
typedef NU8 TY50999[16];
struct TNimType {
NI size;
NU8 kind;
NU8 flags;
TNimType* base;
TNimNode* node;
void* finalizer;
};
struct TNimObject {
TNimType* m_type;
};
struct TY49005 {
  TNimObject Sup;
NI Id;
};
struct TY50539 {
NU8 K;
NU8 S;
NU8 Flags;
TY50551* T;
TY47008* R;
NI A;
};
struct TY50551 {
  TY49005 Sup;
NU8 Kind;
TY50549* Sons;
TY50525* N;
NU8 Flags;
NU8 Callconv;
TY50547* Owner;
TY50547* Sym;
NI64 Size;
NI Align;
NI Containerid;
TY50539 Loc;
};
struct TY50529 {
TNimType* m_type;
NI Counter;
TY50527* Data;
};
struct TY50547 {
  TY49005 Sup;
NU8 Kind;
NU8 Magic;
TY50551* Typ;
TY49011* Name;
TY42532 Info;
TY50547* Owner;
NU32 Flags;
TY50529 Tab;
TY50525* Ast;
NU32 Options;
NI Position;
NI Offset;
TY50539 Loc;
TY50543* Annex;
};
struct TY49011 {
  TY49005 Sup;
NimStringDesc* S;
TY49011* Next;
NI H;
};
struct TY70013 {
  TNimObject Sup;
NU8 Kind;
FILE* F;
NimStringDesc* S;
NI Rd;
NI Wr;
};
struct TNimNode {
NU8 kind;
NI offset;
TNimType* typ;
NCSTRING name;
NI len;
TNimNode** sons;
};
struct TY47008 {
  TNimObject Sup;
TY47008* Left;
TY47008* Right;
NI Length;
NimStringDesc* Data;
};
struct TY38013 {
  TNimObject Sup;
TY38013* Prev;
TY38013* Next;
};
struct TY50543 {
  TY38013 Sup;
NU8 Kind;
NIM_BOOL Generated;
TY47008* Name;
TY50525* Path;
};
struct TY50519 {
  TGenericSeq Sup;
  TY50525* data[SEQ_DECL_SIZE];
};
struct TY50549 {
  TGenericSeq Sup;
  TY50551* data[SEQ_DECL_SIZE];
};
struct TY50527 {
  TGenericSeq Sup;
  TY50547* data[SEQ_DECL_SIZE];
};
N_NIMCALL(void, Invalidpragma_85032)(TY50525* N_85034);
N_NIMCALL(void, Limessage_42562)(TY42532 Info_42564, NU8 Msg_42565, NimStringDesc* Arg_42566);
N_NIMCALL(NimStringDesc*, Rendertree_80042)(TY50525* N_80044, NU8 Renderflags_80047);
N_NIMCALL(TY50525*, Getarg_85036)(TY50525* N_85038, NimStringDesc* Name_85039, NI Pos_85040);
N_NIMCALL(NI, Sonslen_50803)(TY50525* N_50805);
static N_INLINE(NI, subInt)(NI A_6003, NI B_6004);
N_NOINLINE(void, raiseOverflow)(void);
N_NOINLINE(void, raiseFieldError)(NimStringDesc* F_5475);
N_NOINLINE(void, raiseIndexError)(void);
N_NIMCALL(NIM_BOOL, Identeq_49028)(TY49011* Id_49030, NimStringDesc* Name_49031);
static N_INLINE(NI, addInt)(NI A_5803, NI B_5804);
N_NIMCALL(NIM_CHAR, Chararg_85014)(TY50525* N_85016, NimStringDesc* Name_85017, NI Pos_85018, NIM_CHAR Default_85019);
N_NIMCALL(NimStringDesc*, Strarg_85020)(TY50525* N_85022, NimStringDesc* Name_85023, NI Pos_85024, NimStringDesc* Default_85025);
N_NIMCALL(NimStringDesc*, copyString)(NimStringDesc* Src_17308);
N_NIMCALL(NIM_BOOL, Boolarg_85026)(TY50525* N_85028, NimStringDesc* Name_85029, NI Pos_85030, NIM_BOOL Default_85031);
N_NIMCALL(TY70013*, Filterstrip_85009)(TY70013* Stdin_85011, NimStringDesc* Filename_85012, TY50525* Call_85013);
N_NIMCALL(TY70013*, Llstreamopen_70025)(NimStringDesc* Data_70027);
N_NIMCALL(NIM_BOOL, Llstreamatend_70071)(TY70013* S_70073);
N_NIMCALL(NimStringDesc*, Llstreamreadline_70048)(TY70013* S_70050);
N_NIMCALL(NimStringDesc*, nsuStrip)(NimStringDesc* S_23981, NIM_BOOL Leading_23982, NIM_BOOL Trailing_23983);
N_NIMCALL(NIM_BOOL, nsuStartsWith)(NimStringDesc* S_24769, NimStringDesc* Prefix_24770);
N_NIMCALL(void, Llstreamwriteln_70067)(TY70013* S_70069, NimStringDesc* Data_70070);
N_NIMCALL(void, Llstreamclose_70040)(TY70013* S_70042);
N_NIMCALL(TY70013*, Filterreplace_85004)(TY70013* Stdin_85006, NimStringDesc* Filename_85007, TY50525* Call_85008);
N_NIMCALL(NimStringDesc*, nsuReplaceStr)(NimStringDesc* S_25324, NimStringDesc* Sub_25325, NimStringDesc* By_25326);
static NIM_CONST TY50999 TMP85211 = {
0xEC, 0xFF, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00,
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00}
;STRING_LITERAL(TMP85212, "sons", 4);
static NIM_CONST TY50999 TMP85213 = {
0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00}
;STRING_LITERAL(TMP85214, "ident", 5);
static NIM_CONST TY50999 TMP85255 = {
0xE0, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00}
;STRING_LITERAL(TMP85256, "intVal", 6);
static NIM_CONST TY50999 TMP85300 = {
0x00, 0xC0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00,
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00}
;STRING_LITERAL(TMP85301, "strVal", 6);
STRING_LITERAL(TMP85363, "true", 4);
STRING_LITERAL(TMP85364, "false", 5);
STRING_LITERAL(TMP85381, "startswith", 10);
STRING_LITERAL(TMP85382, "", 0);
STRING_LITERAL(TMP85383, "leading", 7);
STRING_LITERAL(TMP85384, "trailing", 8);
STRING_LITERAL(TMP85399, "sub", 3);
STRING_LITERAL(TMP85400, "by", 2);
N_NIMCALL(void, Invalidpragma_85032)(TY50525* N_85034) {
NimStringDesc* LOC1;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "invalidPragma";
F.prev = framePtr;
F.filename = "rod/filters.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 24;F.filename = "filters.nim";
LOC1 = 0;
LOC1 = Rendertree_80042(N_85034, 4);
Limessage_42562((*N_85034).Info, ((NU8) 159), LOC1);
framePtr = framePtr->prev;
}
static N_INLINE(NI, subInt)(NI A_6003, NI B_6004) {
NI Result_6005;
NIM_BOOL LOC2;
Result_6005 = 0;
Result_6005 = (NI64)((NU64)(A_6003) - (NU64)(B_6004));
LOC2 = (0 <= (NI64)(Result_6005 ^ A_6003));
if (LOC2) goto LA3;
LOC2 = (0 <= (NI64)(Result_6005 ^ (NI64)((NU64) ~(B_6004))));
LA3: ;
if (!LOC2) goto LA4;
goto BeforeRet;
LA4: ;
raiseOverflow();
BeforeRet: ;
return Result_6005;
}
static N_INLINE(NI, addInt)(NI A_5803, NI B_5804) {
NI Result_5805;
NIM_BOOL LOC2;
Result_5805 = 0;
Result_5805 = (NI64)((NU64)(A_5803) + (NU64)(B_5804));
LOC2 = (0 <= (NI64)(Result_5805 ^ A_5803));
if (LOC2) goto LA3;
LOC2 = (0 <= (NI64)(Result_5805 ^ B_5804));
LA3: ;
if (!LOC2) goto LA4;
goto BeforeRet;
LA4: ;
raiseOverflow();
BeforeRet: ;
return Result_5805;
}
N_NIMCALL(TY50525*, Getarg_85036)(TY50525* N_85038, NimStringDesc* Name_85039, NI Pos_85040) {
TY50525* Result_85041;
NI I_85076;
NI HEX3Atmp_85206;
NI LOC4;
NI Res_85208;
NIM_BOOL LOC13;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "getArg";
F.prev = framePtr;
F.filename = "rod/filters.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_85041 = 0;
F.line = 27;F.filename = "filters.nim";
Result_85041 = NIM_NIL;
F.line = 28;F.filename = "filters.nim";
if (!((*N_85038).Kind >= ((NU8) 1) && (*N_85038).Kind <= ((NU8) 18))) goto LA2;
F.line = 28;F.filename = "filters.nim";
goto BeforeRet;
LA2: ;
I_85076 = 0;
HEX3Atmp_85206 = 0;
F.line = 29;F.filename = "filters.nim";
LOC4 = Sonslen_50803(N_85038);
HEX3Atmp_85206 = subInt(LOC4, 1);
Res_85208 = 0;
F.line = 1021;F.filename = "system.nim";
Res_85208 = 1;
F.line = 1022;F.filename = "system.nim";
while (1) {
if (!(Res_85208 <= HEX3Atmp_85206)) goto LA5;
F.line = 1021;F.filename = "system.nim";
I_85076 = Res_85208;
F.line = 30;F.filename = "filters.nim";
if (((TMP85211[(*N_85038).Kind/8] &(1<<((*N_85038).Kind%8)))!=0)) raiseFieldError(((NimStringDesc*) &TMP85212));
if ((NU)(I_85076) >= (NU)((*N_85038).KindU.S6.Sons->Sup.len)) raiseIndexError();
if (!((*(*N_85038).KindU.S6.Sons->data[I_85076]).Kind == ((NU8) 23))) goto LA7;
F.line = 31;F.filename = "filters.nim";
if (((TMP85211[(*N_85038).Kind/8] &(1<<((*N_85038).Kind%8)))!=0)) raiseFieldError(((NimStringDesc*) &TMP85212));
if ((NU)(I_85076) >= (NU)((*N_85038).KindU.S6.Sons->Sup.len)) raiseIndexError();
if (((TMP85211[(*(*N_85038).KindU.S6.Sons->data[I_85076]).Kind/8] &(1<<((*(*N_85038).KindU.S6.Sons->data[I_85076]).Kind%8)))!=0)) raiseFieldError(((NimStringDesc*) &TMP85212));
if ((NU)(0) >= (NU)((*(*N_85038).KindU.S6.Sons->data[I_85076]).KindU.S6.Sons->Sup.len)) raiseIndexError();
if (!!(((*(*(*N_85038).KindU.S6.Sons->data[I_85076]).KindU.S6.Sons->data[0]).Kind == ((NU8) 2)))) goto LA10;
F.line = 31;F.filename = "filters.nim";
Invalidpragma_85032(N_85038);
LA10: ;
F.line = 32;F.filename = "filters.nim";
if (((TMP85211[(*N_85038).Kind/8] &(1<<((*N_85038).Kind%8)))!=0)) raiseFieldError(((NimStringDesc*) &TMP85212));
if ((NU)(I_85076) >= (NU)((*N_85038).KindU.S6.Sons->Sup.len)) raiseIndexError();
if (((TMP85211[(*(*N_85038).KindU.S6.Sons->data[I_85076]).Kind/8] &(1<<((*(*N_85038).KindU.S6.Sons->data[I_85076]).Kind%8)))!=0)) raiseFieldError(((NimStringDesc*) &TMP85212));
if ((NU)(0) >= (NU)((*(*N_85038).KindU.S6.Sons->data[I_85076]).KindU.S6.Sons->Sup.len)) raiseIndexError();
if (!(((TMP85213[(*(*(*N_85038).KindU.S6.Sons->data[I_85076]).KindU.S6.Sons->data[0]).Kind/8] &(1<<((*(*(*N_85038).KindU.S6.Sons->data[I_85076]).KindU.S6.Sons->data[0]).Kind%8)))!=0))) raiseFieldError(((NimStringDesc*) &TMP85214));
LOC13 = Identeq_49028((*(*(*N_85038).KindU.S6.Sons->data[I_85076]).KindU.S6.Sons->data[0]).KindU.S5.Ident, Name_85039);
if (!LOC13) goto LA14;
F.line = 33;F.filename = "filters.nim";
F.line = 33;F.filename = "filters.nim";
if (((TMP85211[(*N_85038).Kind/8] &(1<<((*N_85038).Kind%8)))!=0)) raiseFieldError(((NimStringDesc*) &TMP85212));
if ((NU)(I_85076) >= (NU)((*N_85038).KindU.S6.Sons->Sup.len)) raiseIndexError();
if (((TMP85211[(*(*N_85038).KindU.S6.Sons->data[I_85076]).Kind/8] &(1<<((*(*N_85038).KindU.S6.Sons->data[I_85076]).Kind%8)))!=0)) raiseFieldError(((NimStringDesc*) &TMP85212));
if ((NU)(1) >= (NU)((*(*N_85038).KindU.S6.Sons->data[I_85076]).KindU.S6.Sons->Sup.len)) raiseIndexError();
Result_85041 = (*(*N_85038).KindU.S6.Sons->data[I_85076]).KindU.S6.Sons->data[1];
goto BeforeRet;
LA14: ;
goto LA6;
LA7: ;
if (!(I_85076 == Pos_85040)) goto LA16;
F.line = 35;F.filename = "filters.nim";
F.line = 35;F.filename = "filters.nim";
if (((TMP85211[(*N_85038).Kind/8] &(1<<((*N_85038).Kind%8)))!=0)) raiseFieldError(((NimStringDesc*) &TMP85212));
if ((NU)(I_85076) >= (NU)((*N_85038).KindU.S6.Sons->Sup.len)) raiseIndexError();
Result_85041 = (*N_85038).KindU.S6.Sons->data[I_85076];
goto BeforeRet;
goto LA6;
LA16: ;
LA6: ;
F.line = 1024;F.filename = "system.nim";
Res_85208 = addInt(Res_85208, 1);
} LA5: ;
BeforeRet: ;
framePtr = framePtr->prev;
return Result_85041;
}
N_NIMCALL(NIM_CHAR, Chararg_85014)(TY50525* N_85016, NimStringDesc* Name_85017, NI Pos_85018, NIM_CHAR Default_85019) {
NIM_CHAR Result_85221;
TY50525* X_85222;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "charArg";
F.prev = framePtr;
F.filename = "rod/filters.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_85221 = 0;
X_85222 = 0;
F.line = 38;F.filename = "filters.nim";
X_85222 = Getarg_85036(N_85016, Name_85017, Pos_85018);
F.line = 39;F.filename = "filters.nim";
if (!(X_85222 == NIM_NIL)) goto LA2;
F.line = 39;F.filename = "filters.nim";
Result_85221 = Default_85019;
goto LA1;
LA2: ;
if (!((*X_85222).Kind == ((NU8) 5))) goto LA4;
F.line = 40;F.filename = "filters.nim";
if (!(((TMP85255[(*X_85222).Kind/8] &(1<<((*X_85222).Kind%8)))!=0))) raiseFieldError(((NimStringDesc*) &TMP85256));
Result_85221 = ((NIM_CHAR) (((NI) (((NI) ((*X_85222).KindU.S1.Intval))))));
goto LA1;
LA4: ;
F.line = 41;F.filename = "filters.nim";
Invalidpragma_85032(N_85016);
LA1: ;
framePtr = framePtr->prev;
return Result_85221;
}
N_NIMCALL(NimStringDesc*, Strarg_85020)(TY50525* N_85022, NimStringDesc* Name_85023, NI Pos_85024, NimStringDesc* Default_85025) {
NimStringDesc* Result_85263;
TY50525* X_85264;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "strArg";
F.prev = framePtr;
F.filename = "rod/filters.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_85263 = 0;
X_85264 = 0;
F.line = 44;F.filename = "filters.nim";
X_85264 = Getarg_85036(N_85022, Name_85023, Pos_85024);
F.line = 45;F.filename = "filters.nim";
if (!(X_85264 == NIM_NIL)) goto LA2;
F.line = 45;F.filename = "filters.nim";
Result_85263 = copyString(Default_85025);
goto LA1;
LA2: ;
if (!((*X_85264).Kind >= ((NU8) 14) && (*X_85264).Kind <= ((NU8) 16))) goto LA4;
F.line = 46;F.filename = "filters.nim";
if (!(((TMP85300[(*X_85264).Kind/8] &(1<<((*X_85264).Kind%8)))!=0))) raiseFieldError(((NimStringDesc*) &TMP85301));
Result_85263 = copyString((*X_85264).KindU.S3.Strval);
goto LA1;
LA4: ;
F.line = 47;F.filename = "filters.nim";
Invalidpragma_85032(N_85022);
LA1: ;
framePtr = framePtr->prev;
return Result_85263;
}
N_NIMCALL(NIM_BOOL, Boolarg_85026)(TY50525* N_85028, NimStringDesc* Name_85029, NI Pos_85030, NIM_BOOL Default_85031) {
NIM_BOOL Result_85308;
TY50525* X_85309;
NIM_BOOL LOC4;
NIM_BOOL LOC8;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "boolArg";
F.prev = framePtr;
F.filename = "rod/filters.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_85308 = 0;
X_85309 = 0;
F.line = 50;F.filename = "filters.nim";
X_85309 = Getarg_85036(N_85028, Name_85029, Pos_85030);
F.line = 51;F.filename = "filters.nim";
if (!(X_85309 == NIM_NIL)) goto LA2;
F.line = 51;F.filename = "filters.nim";
Result_85308 = Default_85031;
goto LA1;
LA2: ;
LOC4 = ((*X_85309).Kind == ((NU8) 2));
if (!(LOC4)) goto LA5;
if (!(((TMP85213[(*X_85309).Kind/8] &(1<<((*X_85309).Kind%8)))!=0))) raiseFieldError(((NimStringDesc*) &TMP85214));
LOC4 = Identeq_49028((*X_85309).KindU.S5.Ident, ((NimStringDesc*) &TMP85363));
LA5: ;
if (!LOC4) goto LA6;
F.line = 52;F.filename = "filters.nim";
Result_85308 = NIM_TRUE;
goto LA1;
LA6: ;
LOC8 = ((*X_85309).Kind == ((NU8) 2));
if (!(LOC8)) goto LA9;
if (!(((TMP85213[(*X_85309).Kind/8] &(1<<((*X_85309).Kind%8)))!=0))) raiseFieldError(((NimStringDesc*) &TMP85214));
LOC8 = Identeq_49028((*X_85309).KindU.S5.Ident, ((NimStringDesc*) &TMP85364));
LA9: ;
if (!LOC8) goto LA10;
F.line = 53;F.filename = "filters.nim";
Result_85308 = NIM_FALSE;
goto LA1;
LA10: ;
F.line = 54;F.filename = "filters.nim";
Invalidpragma_85032(N_85028);
LA1: ;
framePtr = framePtr->prev;
return Result_85308;
}
N_NIMCALL(TY70013*, Filterstrip_85009)(TY70013* Stdin_85011, NimStringDesc* Filename_85012, TY50525* Call_85013) {
TY70013* Result_85370;
NimStringDesc* Pattern_85371;
NIM_BOOL Leading_85372;
NIM_BOOL Trailing_85373;
NIM_BOOL LOC2;
NimStringDesc* Line_85374;
NimStringDesc* Stripped_85375;
NIM_BOOL LOC4;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "filterStrip";
F.prev = framePtr;
F.filename = "rod/filters.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_85370 = 0;
Pattern_85371 = 0;
F.line = 57;F.filename = "filters.nim";
Pattern_85371 = Strarg_85020(Call_85013, ((NimStringDesc*) &TMP85381), 1, ((NimStringDesc*) &TMP85382));
Leading_85372 = 0;
F.line = 58;F.filename = "filters.nim";
Leading_85372 = Boolarg_85026(Call_85013, ((NimStringDesc*) &TMP85383), 2, NIM_TRUE);
Trailing_85373 = 0;
F.line = 59;F.filename = "filters.nim";
Trailing_85373 = Boolarg_85026(Call_85013, ((NimStringDesc*) &TMP85384), 3, NIM_TRUE);
F.line = 60;F.filename = "filters.nim";
Result_85370 = Llstreamopen_70025(((NimStringDesc*) &TMP85382));
F.line = 61;F.filename = "filters.nim";
while (1) {
LOC2 = Llstreamatend_70071(Stdin_85011);
if (!!(LOC2)) goto LA1;
Line_85374 = 0;
F.line = 62;F.filename = "filters.nim";
Line_85374 = Llstreamreadline_70048(Stdin_85011);
Stripped_85375 = 0;
F.line = 63;F.filename = "filters.nim";
Stripped_85375 = nsuStrip(Line_85374, Leading_85372, Trailing_85373);
F.line = 64;F.filename = "filters.nim";
LOC4 = (Pattern_85371->Sup.len == 0);
if (LOC4) goto LA5;
LOC4 = nsuStartsWith(Stripped_85375, Pattern_85371);
LA5: ;
if (!LOC4) goto LA6;
F.line = 65;F.filename = "filters.nim";
Llstreamwriteln_70067(Result_85370, Stripped_85375);
goto LA3;
LA6: ;
F.line = 67;F.filename = "filters.nim";
Llstreamwriteln_70067(Result_85370, Line_85374);
LA3: ;
} LA1: ;
F.line = 68;F.filename = "filters.nim";
Llstreamclose_70040(Stdin_85011);
framePtr = framePtr->prev;
return Result_85370;
}
N_NIMCALL(TY70013*, Filterreplace_85004)(TY70013* Stdin_85006, NimStringDesc* Filename_85007, TY50525* Call_85008) {
TY70013* Result_85390;
NimStringDesc* Sub_85391;
NimStringDesc* By_85396;
NIM_BOOL LOC5;
NimStringDesc* Line_85397;
NimStringDesc* LOC6;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "filterReplace";
F.prev = framePtr;
F.filename = "rod/filters.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_85390 = 0;
Sub_85391 = 0;
F.line = 71;F.filename = "filters.nim";
Sub_85391 = Strarg_85020(Call_85008, ((NimStringDesc*) &TMP85399), 1, ((NimStringDesc*) &TMP85382));
F.line = 72;F.filename = "filters.nim";
if (!(Sub_85391->Sup.len == 0)) goto LA2;
F.line = 72;F.filename = "filters.nim";
Invalidpragma_85032(Call_85008);
LA2: ;
By_85396 = 0;
F.line = 73;F.filename = "filters.nim";
By_85396 = Strarg_85020(Call_85008, ((NimStringDesc*) &TMP85400), 2, ((NimStringDesc*) &TMP85382));
F.line = 74;F.filename = "filters.nim";
Result_85390 = Llstreamopen_70025(((NimStringDesc*) &TMP85382));
F.line = 75;F.filename = "filters.nim";
while (1) {
LOC5 = Llstreamatend_70071(Stdin_85006);
if (!!(LOC5)) goto LA4;
Line_85397 = 0;
F.line = 76;F.filename = "filters.nim";
Line_85397 = Llstreamreadline_70048(Stdin_85006);
F.line = 77;F.filename = "filters.nim";
LOC6 = 0;
LOC6 = nsuReplaceStr(Line_85397, Sub_85391, By_85396);
Llstreamwriteln_70067(Result_85390, LOC6);
} LA4: ;
F.line = 78;F.filename = "filters.nim";
Llstreamclose_70040(Stdin_85006);
framePtr = framePtr->prev;
return Result_85390;
}
N_NOINLINE(void, filtersInit)(void) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "filters";
F.prev = framePtr;
F.filename = "rod/filters.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
framePtr = framePtr->prev;
}

