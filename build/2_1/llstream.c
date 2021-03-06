/* Generated by Nimrod Compiler v0.8.9 */
/*   (c) 2010 Andreas Rumpf */

typedef long int NI;
typedef unsigned long int NU;
#include "nimbase.h"

#include <pthread.h>
typedef struct TY73013 TY73013;
typedef struct NimStringDesc NimStringDesc;
typedef struct TGenericSeq TGenericSeq;
typedef struct TNimType TNimType;
typedef struct TNimNode TNimNode;
typedef struct TNimObject TNimObject;
typedef struct TY10802 TY10802;
typedef struct TY11190 TY11190;
typedef struct TY10818 TY10818;
typedef struct TY10814 TY10814;
typedef struct TY10810 TY10810;
typedef struct TY11188 TY11188;
struct TGenericSeq {
NI len;
NI space;
};
typedef NIM_CHAR TY239[100000001];
struct NimStringDesc {
  TGenericSeq Sup;
TY239 data;
};
struct TNimType {
NI size;
NU8 kind;
NU8 flags;
TNimType* base;
TNimNode* node;
void* finalizer;
};
struct TNimNode {
NU8 kind;
NI offset;
TNimType* typ;
NCSTRING name;
NI len;
TNimNode** sons;
};
struct TNimObject {
TNimType* m_type;
};
struct TY73013 {
  TNimObject Sup;
NU8 Kind;
FILE* F;
NimStringDesc* S;
NI Rd;
NI Wr;
};
struct TY10802 {
NI Refcount;
TNimType* Typ;
};
struct TY10818 {
NI Len;
NI Cap;
TY10802** D;
};
struct TY10814 {
NI Counter;
NI Max;
TY10810* Head;
TY10810** Data;
};
struct TY11188 {
NI Stackscans;
NI Cyclecollections;
NI Maxthreshold;
NI Maxstacksize;
NI Maxstackcells;
NI Cycletablesize;
};
struct TY11190 {
TY10818 Zct;
TY10818 Decstack;
TY10814 Cycleroots;
TY10818 Tempstack;
NI Cyclerootslock;
NI Zctlock;
TY11188 Stat;
};
typedef NI TY8814[16];
struct TY10810 {
TY10810* Next;
NI Key;
TY8814 Bits;
};
N_NIMCALL(TY73013*, Llstreamopen_73025)(NimStringDesc* Data_73027);
N_NIMCALL(void*, newObj)(TNimType* Typ_12507, NI Size_12508);
static N_INLINE(void, asgnRefNoCycle)(void** Dest_12018, void* Src_12019);
static N_INLINE(TY10802*, Usrtocell_11236)(void* Usr_11238);
static N_INLINE(NI, Atomicinc_3001)(NI* Memloc_3004, NI X_3005);
static N_INLINE(NI, Atomicdec_3006)(NI* Memloc_3009, NI X_3010);
static N_INLINE(void, Rtladdzct_11858)(TY10802* C_11860);
N_NOINLINE(void, Addzct_11225)(TY10818* S_11228, TY10802* C_11229);
N_NIMCALL(NimStringDesc*, copyString)(NimStringDesc* Src_17508);
N_NIMCALL(TY73013*, Llstreamopen_73028)(FILE** F_73031);
N_NIMCALL(TY73013*, Llstreamopen_73032)(NimStringDesc* Filename_73034, NU8 Mode_73035);
N_NIMCALL(NIM_BOOL, Open_3617)(FILE** F_3620, NimStringDesc* Filename_3621, NU8 Mode_3622, NI Bufsize_3623);
N_NIMCALL(TY73013*, Llstreamopen_73036)(void);
N_NIMCALL(TY73013*, Llstreamopenstdin_73038)(void);
N_NIMCALL(void, Llstreamclose_73040)(TY73013* S_73042);
N_NIMCALL(NI, Llreadfromstdin_73178)(TY73013* S_73180, void* Buf_73181, NI Buflen_73182);
N_NIMCALL(void, Write_3658)(FILE* F_3660, NimStringDesc* S_3661);
N_NIMCALL(NimStringDesc*, Readline_3679)(FILE* F_3681);
static N_INLINE(void, appendString)(NimStringDesc* Dest_17592, NimStringDesc* Src_17593);
N_NIMCALL(NimStringDesc*, resizeString)(NimStringDesc* Dest_17582, NI Addlen_17583);
static N_INLINE(NI, subInt)(NI A_6003, NI B_6004);
N_NOINLINE(void, raiseOverflow)(void);
static N_INLINE(NI, addInt)(NI A_5803, NI B_5804);
N_NOINLINE(void, raiseIndexError)(void);
N_NIMCALL(NI, Llstreamread_73043)(TY73013* S_73045, void* Buf_73046, NI Buflen_73047);
N_NIMCALL(NI, Readbuffer_3714)(FILE* F_3716, void* Buffer_3717, NI Len_3718);
N_NIMCALL(NimStringDesc*, Llstreamreadline_73048)(TY73013* S_73050);
N_NIMCALL(NimStringDesc*, addChar)(NimStringDesc* S_1603, NIM_CHAR C_1604);
N_NIMCALL(NIM_BOOL, Llstreamatend_73071)(TY73013* S_73073);
N_NIMCALL(NIM_BOOL, Endoffile_3638)(FILE* F_3640);
N_NIMCALL(void, Llstreamwrite_73054)(TY73013* S_73056, NimStringDesc* Data_73057);
N_NIMCALL(void, Llstreamwriteln_73067)(TY73013* S_73069, NimStringDesc* Data_73070);
N_NIMCALL(void, Llstreamwrite_73058)(TY73013* S_73060, NIM_CHAR Data_73061);
N_NIMCALL(NI, Writebuffer_3733)(FILE* F_3735, void* Buffer_3736, NI Len_3737);
N_NIMCALL(void, Llstreamwrite_73062)(TY73013* S_73064, void* Buf_73065, NI Buflen_73066);
N_NIMCALL(NimStringDesc*, setLengthStr)(NimStringDesc* S_17625, NI Newlen_17626);
N_NIMCALL(NimStringDesc*, Llstreamreadall_73051)(TY73013* S_73053);
N_NIMCALL(NimStringDesc*, copyStr)(NimStringDesc* S_1924, NI First_1925);
N_NIMCALL(NimStringDesc*, mnewString)(NI Len_1349);
STRING_LITERAL(TMP73174, "", 0);
STRING_LITERAL(TMP73212, "Nimrod> ", 8);
STRING_LITERAL(TMP73213, "\012", 1);
extern TNimType* NTI73015; /* PLLStream */
extern TNimType* NTI73013; /* TLLStream */
extern TY11190 Gch_11210;
static N_INLINE(TY10802*, Usrtocell_11236)(void* Usr_11238) {
TY10802* Result_11239;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "usrToCell";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_11239 = 0;
F.line = 100;F.filename = "gc.nim";
Result_11239 = ((TY10802*) ((NI32)((NU32)(((NI) (Usr_11238))) - (NU32)(((NI) (((NI)sizeof(TY10802))))))));
framePtr = framePtr->prev;
return Result_11239;
}
static N_INLINE(NI, Atomicinc_3001)(NI* Memloc_3004, NI X_3005) {
NI Result_7408;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "atomicInc";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/systhread.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_7408 = 0;
F.line = 29;F.filename = "systhread.nim";
Result_7408 = __sync_add_and_fetch(Memloc_3004, X_3005);
framePtr = framePtr->prev;
return Result_7408;
}
static N_INLINE(NI, Atomicdec_3006)(NI* Memloc_3009, NI X_3010) {
NI Result_7606;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "atomicDec";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/systhread.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_7606 = 0;
F.line = 37;F.filename = "systhread.nim";
Result_7606 = __sync_sub_and_fetch(Memloc_3009, X_3010);
framePtr = framePtr->prev;
return Result_7606;
}
static N_INLINE(void, Rtladdzct_11858)(TY10802* C_11860) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "rtlAddZCT";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 211;F.filename = "gc.nim";
if (!NIM_TRUE) goto LA2;
F.line = 211;F.filename = "gc.nim";
pthread_mutex_lock(&Gch_11210.Zctlock);
LA2: ;
F.line = 212;F.filename = "gc.nim";
Addzct_11225(&Gch_11210.Zct, C_11860);
F.line = 213;F.filename = "gc.nim";
if (!NIM_TRUE) goto LA5;
F.line = 213;F.filename = "gc.nim";
pthread_mutex_unlock(&Gch_11210.Zctlock);
LA5: ;
framePtr = framePtr->prev;
}
static N_INLINE(void, asgnRefNoCycle)(void** Dest_12018, void* Src_12019) {
TY10802* C_12020;
NI LOC4;
TY10802* C_12022;
NI LOC9;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "asgnRefNoCycle";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 244;F.filename = "gc.nim";
if (!!((Src_12019 == NIM_NIL))) goto LA2;
C_12020 = 0;
F.line = 245;F.filename = "gc.nim";
C_12020 = Usrtocell_11236(Src_12019);
F.line = 246;F.filename = "gc.nim";
LOC4 = Atomicinc_3001(&(*C_12020).Refcount, 8);
LA2: ;
F.line = 247;F.filename = "gc.nim";
if (!!(((*Dest_12018) == NIM_NIL))) goto LA6;
C_12022 = 0;
F.line = 248;F.filename = "gc.nim";
C_12022 = Usrtocell_11236((*Dest_12018));
F.line = 249;F.filename = "gc.nim";
LOC9 = Atomicdec_3006(&(*C_12022).Refcount, 8);
if (!((NU32)(LOC9) < (NU32)(8))) goto LA10;
F.line = 250;F.filename = "gc.nim";
Rtladdzct_11858(C_12022);
LA10: ;
LA6: ;
F.line = 251;F.filename = "gc.nim";
(*Dest_12018) = Src_12019;
framePtr = framePtr->prev;
}
N_NIMCALL(TY73013*, Llstreamopen_73025)(NimStringDesc* Data_73027) {
TY73013* Result_73077;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamOpen";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_73077 = 0;
F.line = 46;F.filename = "llstream.nim";
Result_73077 = (TY73013*) newObj(NTI73015, sizeof(TY73013));
(*Result_73077).Sup.m_type = NTI73013;
F.line = 47;F.filename = "llstream.nim";
asgnRefNoCycle((void**) &(*Result_73077).S, copyString(Data_73027));
F.line = 48;F.filename = "llstream.nim";
(*Result_73077).Kind = ((NU8) 1);
framePtr = framePtr->prev;
return Result_73077;
}
N_NIMCALL(TY73013*, Llstreamopen_73028)(FILE** F_73031) {
TY73013* Result_73101;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamOpen";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_73101 = 0;
F.line = 51;F.filename = "llstream.nim";
Result_73101 = (TY73013*) newObj(NTI73015, sizeof(TY73013));
(*Result_73101).Sup.m_type = NTI73013;
F.line = 52;F.filename = "llstream.nim";
(*Result_73101).F = (*F_73031);
F.line = 53;F.filename = "llstream.nim";
(*Result_73101).Kind = ((NU8) 2);
framePtr = framePtr->prev;
return Result_73101;
}
N_NIMCALL(TY73013*, Llstreamopen_73032)(NimStringDesc* Filename_73034, NU8 Mode_73035) {
TY73013* Result_73121;
NIM_BOOL LOC2;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamOpen";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_73121 = 0;
F.line = 56;F.filename = "llstream.nim";
Result_73121 = (TY73013*) newObj(NTI73015, sizeof(TY73013));
(*Result_73121).Sup.m_type = NTI73013;
F.line = 57;F.filename = "llstream.nim";
(*Result_73121).Kind = ((NU8) 2);
F.line = 58;F.filename = "llstream.nim";
LOC2 = Open_3617(&(*Result_73121).F, Filename_73034, Mode_73035, -1);
if (!!(LOC2)) goto LA3;
F.line = 58;F.filename = "llstream.nim";
Result_73121 = NIM_NIL;
LA3: ;
framePtr = framePtr->prev;
return Result_73121;
}
N_NIMCALL(TY73013*, Llstreamopen_73036)(void) {
TY73013* Result_73140;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamOpen";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_73140 = 0;
F.line = 61;F.filename = "llstream.nim";
Result_73140 = (TY73013*) newObj(NTI73015, sizeof(TY73013));
(*Result_73140).Sup.m_type = NTI73013;
F.line = 62;F.filename = "llstream.nim";
(*Result_73140).Kind = ((NU8) 0);
framePtr = framePtr->prev;
return Result_73140;
}
N_NIMCALL(TY73013*, Llstreamopenstdin_73038)(void) {
TY73013* Result_73158;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamOpenStdIn";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_73158 = 0;
F.line = 65;F.filename = "llstream.nim";
Result_73158 = (TY73013*) newObj(NTI73015, sizeof(TY73013));
(*Result_73158).Sup.m_type = NTI73013;
F.line = 66;F.filename = "llstream.nim";
(*Result_73158).Kind = ((NU8) 3);
F.line = 67;F.filename = "llstream.nim";
asgnRefNoCycle((void**) &(*Result_73158).S, copyString(((NimStringDesc*) &TMP73174)));
framePtr = framePtr->prev;
return Result_73158;
}
N_NIMCALL(void, Llstreamclose_73040)(TY73013* S_73042) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamClose";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 70;F.filename = "llstream.nim";
switch ((*S_73042).Kind) {
case ((NU8) 0):
case ((NU8) 1):
case ((NU8) 3):
break;
case ((NU8) 2):
F.line = 74;F.filename = "llstream.nim";
fclose((*S_73042).F);
break;
}
framePtr = framePtr->prev;
}
static N_INLINE(void, appendString)(NimStringDesc* Dest_17592, NimStringDesc* Src_17593) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "appendString";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/sysstr.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 150;F.filename = "sysstr.nim";
memcpy(((NCSTRING) (&(*Dest_17592).data[((*Dest_17592).Sup.len)-0])), ((NCSTRING) ((*Src_17593).data)), ((int) ((NI32)((NI32)((*Src_17593).Sup.len + 1) * 1))));
F.line = 151;F.filename = "sysstr.nim";
(*Dest_17592).Sup.len += (*Src_17593).Sup.len;
framePtr = framePtr->prev;
}
static N_INLINE(NI, subInt)(NI A_6003, NI B_6004) {
NI Result_6005;
NIM_BOOL LOC2;
Result_6005 = 0;
Result_6005 = (NI32)((NU32)(A_6003) - (NU32)(B_6004));
LOC2 = (0 <= (NI32)(Result_6005 ^ A_6003));
if (LOC2) goto LA3;
LOC2 = (0 <= (NI32)(Result_6005 ^ (NI32)((NU32) ~(B_6004))));
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
Result_5805 = (NI32)((NU32)(A_5803) + (NU32)(B_5804));
LOC2 = (0 <= (NI32)(Result_5805 ^ A_5803));
if (LOC2) goto LA3;
LOC2 = (0 <= (NI32)(Result_5805 ^ B_5804));
LA3: ;
if (!LOC2) goto LA4;
goto BeforeRet;
LA4: ;
raiseOverflow();
BeforeRet: ;
return Result_5805;
}
N_NIMCALL(NI, Llreadfromstdin_73178)(TY73013* S_73180, void* Buf_73181, NI Buflen_73182) {
NI Result_73183;
NimStringDesc* Line_73184;
NI L_73185;
NIM_BOOL LOC3;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLreadFromStdin";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_73183 = 0;
Line_73184 = 0;
L_73185 = 0;
F.line = 80;F.filename = "llstream.nim";
asgnRefNoCycle((void**) &(*S_73180).S, copyString(((NimStringDesc*) &TMP73174)));
F.line = 81;F.filename = "llstream.nim";
(*S_73180).Rd = 0;
F.line = 82;F.filename = "llstream.nim";
while (1) {
F.line = 83;F.filename = "llstream.nim";
Write_3658(stdout, ((NimStringDesc*) &TMP73212));
F.line = 84;F.filename = "llstream.nim";
Line_73184 = Readline_3679(stdin);
F.line = 85;F.filename = "llstream.nim";
L_73185 = Line_73184->Sup.len;
F.line = 86;F.filename = "llstream.nim";
(*S_73180).S = resizeString((*S_73180).S, Line_73184->Sup.len + 0);
appendString((*S_73180).S, Line_73184);
F.line = 87;F.filename = "llstream.nim";
(*S_73180).S = resizeString((*S_73180).S, 1);
appendString((*S_73180).S, ((NimStringDesc*) &TMP73213));
F.line = 88;F.filename = "llstream.nim";
LOC3 = (0 < L_73185);
if (!(LOC3)) goto LA4;
if ((NU)(addInt(subInt(L_73185, 1), 0)) > (NU)(Line_73184->Sup.len)) raiseIndexError();
LOC3 = ((NU8)(Line_73184->data[addInt(subInt(L_73185, 1), 0)]) == (NU8)(35));
LA4: ;
if (!LOC3) goto LA5;
F.line = 88;F.filename = "llstream.nim";
goto LA1;
LA5: ;
} LA1: ;
F.line = 89;F.filename = "llstream.nim";
Result_73183 = ((Buflen_73182 <= subInt((*S_73180).S->Sup.len, (*S_73180).Rd)) ? Buflen_73182 : subInt((*S_73180).S->Sup.len, (*S_73180).Rd));
F.line = 90;F.filename = "llstream.nim";
if (!(0 < Result_73183)) goto LA8;
F.line = 91;F.filename = "llstream.nim";
if ((NU)(addInt(0, (*S_73180).Rd)) > (NU)((*S_73180).S->Sup.len)) raiseIndexError();
memcpy(Buf_73181, ((void*) (&(*S_73180).S->data[addInt(0, (*S_73180).Rd)])), Result_73183);
F.line = 92;F.filename = "llstream.nim";
(*S_73180).Rd = addInt((*S_73180).Rd, Result_73183);
LA8: ;
framePtr = framePtr->prev;
return Result_73183;
}
N_NIMCALL(NI, Llstreamread_73043)(TY73013* S_73045, void* Buf_73046, NI Buflen_73047) {
NI Result_73219;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamRead";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_73219 = 0;
F.line = 95;F.filename = "llstream.nim";
switch ((*S_73045).Kind) {
case ((NU8) 0):
F.line = 97;F.filename = "llstream.nim";
Result_73219 = 0;
break;
case ((NU8) 1):
F.line = 99;F.filename = "llstream.nim";
Result_73219 = ((Buflen_73047 <= subInt((*S_73045).S->Sup.len, (*S_73045).Rd)) ? Buflen_73047 : subInt((*S_73045).S->Sup.len, (*S_73045).Rd));
F.line = 100;F.filename = "llstream.nim";
if (!(0 < Result_73219)) goto LA2;
F.line = 101;F.filename = "llstream.nim";
if ((NU)(addInt(0, (*S_73045).Rd)) > (NU)((*S_73045).S->Sup.len)) raiseIndexError();
memcpy(Buf_73046, ((void*) (&(*S_73045).S->data[addInt(0, (*S_73045).Rd)])), Result_73219);
F.line = 102;F.filename = "llstream.nim";
(*S_73045).Rd = addInt((*S_73045).Rd, Result_73219);
LA2: ;
break;
case ((NU8) 2):
F.line = 104;F.filename = "llstream.nim";
Result_73219 = Readbuffer_3714((*S_73045).F, Buf_73046, Buflen_73047);
break;
case ((NU8) 3):
F.line = 106;F.filename = "llstream.nim";
Result_73219 = Llreadfromstdin_73178(S_73045, Buf_73046, Buflen_73047);
break;
}
framePtr = framePtr->prev;
return Result_73219;
}
N_NIMCALL(NimStringDesc*, Llstreamreadline_73048)(TY73013* S_73050) {
NimStringDesc* Result_73242;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamReadLine";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_73242 = 0;
F.line = 109;F.filename = "llstream.nim";
switch ((*S_73050).Kind) {
case ((NU8) 0):
F.line = 111;F.filename = "llstream.nim";
Result_73242 = copyString(((NimStringDesc*) &TMP73174));
break;
case ((NU8) 1):
F.line = 113;F.filename = "llstream.nim";
Result_73242 = copyString(((NimStringDesc*) &TMP73174));
F.line = 114;F.filename = "llstream.nim";
while (1) {
if (!((*S_73050).Rd < (*S_73050).S->Sup.len)) goto LA1;
F.line = 115;F.filename = "llstream.nim";
if ((NU)(addInt((*S_73050).Rd, 0)) > (NU)((*S_73050).S->Sup.len)) raiseIndexError();
switch (((NU8)((*S_73050).S->data[addInt((*S_73050).Rd, 0)]))) {
case 13:
F.line = 117;F.filename = "llstream.nim";
(*S_73050).Rd = addInt((*S_73050).Rd, 1);
F.line = 118;F.filename = "llstream.nim";
if ((NU)(addInt((*S_73050).Rd, 0)) > (NU)((*S_73050).S->Sup.len)) raiseIndexError();
if (!((NU8)((*S_73050).S->data[addInt((*S_73050).Rd, 0)]) == (NU8)(10))) goto LA3;
F.line = 118;F.filename = "llstream.nim";
(*S_73050).Rd = addInt((*S_73050).Rd, 1);
LA3: ;
F.line = 119;F.filename = "llstream.nim";
goto LA1;
break;
case 10:
F.line = 121;F.filename = "llstream.nim";
(*S_73050).Rd = addInt((*S_73050).Rd, 1);
F.line = 122;F.filename = "llstream.nim";
goto LA1;
break;
default:
F.line = 124;F.filename = "llstream.nim";
if ((NU)(addInt((*S_73050).Rd, 0)) > (NU)((*S_73050).S->Sup.len)) raiseIndexError();
Result_73242 = addChar(Result_73242, (*S_73050).S->data[addInt((*S_73050).Rd, 0)]);
F.line = 125;F.filename = "llstream.nim";
(*S_73050).Rd = addInt((*S_73050).Rd, 1);
break;
}
} LA1: ;
break;
case ((NU8) 2):
F.line = 127;F.filename = "llstream.nim";
Result_73242 = Readline_3679((*S_73050).F);
break;
case ((NU8) 3):
F.line = 129;F.filename = "llstream.nim";
Result_73242 = Readline_3679(stdin);
break;
}
framePtr = framePtr->prev;
return Result_73242;
}
N_NIMCALL(NIM_BOOL, Llstreamatend_73071)(TY73013* S_73073) {
NIM_BOOL Result_73301;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamAtEnd";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_73301 = 0;
F.line = 132;F.filename = "llstream.nim";
switch ((*S_73073).Kind) {
case ((NU8) 0):
F.line = 133;F.filename = "llstream.nim";
Result_73301 = NIM_TRUE;
break;
case ((NU8) 1):
F.line = 134;F.filename = "llstream.nim";
Result_73301 = ((*S_73073).S->Sup.len <= (*S_73073).Rd);
break;
case ((NU8) 2):
F.line = 135;F.filename = "llstream.nim";
Result_73301 = Endoffile_3638((*S_73073).F);
break;
case ((NU8) 3):
F.line = 136;F.filename = "llstream.nim";
Result_73301 = NIM_FALSE;
break;
}
framePtr = framePtr->prev;
return Result_73301;
}
N_NIMCALL(void, Llstreamwrite_73054)(TY73013* S_73056, NimStringDesc* Data_73057) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamWrite";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 139;F.filename = "llstream.nim";
switch ((*S_73056).Kind) {
case ((NU8) 0):
case ((NU8) 3):
break;
case ((NU8) 1):
F.line = 143;F.filename = "llstream.nim";
(*S_73056).S = resizeString((*S_73056).S, Data_73057->Sup.len + 0);
appendString((*S_73056).S, Data_73057);
F.line = 144;F.filename = "llstream.nim";
(*S_73056).Wr = addInt((*S_73056).Wr, Data_73057->Sup.len);
break;
case ((NU8) 2):
F.line = 146;F.filename = "llstream.nim";
Write_3658((*S_73056).F, Data_73057);
break;
}
framePtr = framePtr->prev;
}
N_NIMCALL(void, Llstreamwriteln_73067)(TY73013* S_73069, NimStringDesc* Data_73070) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamWriteln";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 149;F.filename = "llstream.nim";
Llstreamwrite_73054(S_73069, Data_73070);
F.line = 150;F.filename = "llstream.nim";
Llstreamwrite_73054(S_73069, ((NimStringDesc*) &TMP73213));
framePtr = framePtr->prev;
}
N_NIMCALL(void, Llstreamwrite_73058)(TY73013* S_73060, NIM_CHAR Data_73061) {
NIM_CHAR C_73332;
NI LOC1;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamWrite";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
C_73332 = 0;
F.line = 154;F.filename = "llstream.nim";
switch ((*S_73060).Kind) {
case ((NU8) 0):
case ((NU8) 3):
break;
case ((NU8) 1):
F.line = 158;F.filename = "llstream.nim";
(*S_73060).S = addChar((*S_73060).S, Data_73061);
F.line = 159;F.filename = "llstream.nim";
(*S_73060).Wr = addInt((*S_73060).Wr, 1);
break;
case ((NU8) 2):
F.line = 161;F.filename = "llstream.nim";
C_73332 = Data_73061;
F.line = 162;F.filename = "llstream.nim";
LOC1 = Writebuffer_3733((*S_73060).F, ((void*) (&C_73332)), 1);
break;
}
framePtr = framePtr->prev;
}
N_NIMCALL(void, Llstreamwrite_73062)(TY73013* S_73064, void* Buf_73065, NI Buflen_73066) {
NI LOC4;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamWrite";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 165;F.filename = "llstream.nim";
switch ((*S_73064).Kind) {
case ((NU8) 0):
case ((NU8) 3):
break;
case ((NU8) 1):
F.line = 169;F.filename = "llstream.nim";
if (!(0 < Buflen_73066)) goto LA2;
F.line = 170;F.filename = "llstream.nim";
(*S_73064).S = setLengthStr((*S_73064).S, addInt((*S_73064).S->Sup.len, Buflen_73066));
F.line = 171;F.filename = "llstream.nim";
if ((NU)(addInt(0, (*S_73064).Wr)) > (NU)((*S_73064).S->Sup.len)) raiseIndexError();
memcpy(((void*) (&(*S_73064).S->data[addInt(0, (*S_73064).Wr)])), Buf_73065, Buflen_73066);
F.line = 172;F.filename = "llstream.nim";
(*S_73064).Wr = addInt((*S_73064).Wr, Buflen_73066);
LA2: ;
break;
case ((NU8) 2):
F.line = 174;F.filename = "llstream.nim";
LOC4 = Writebuffer_3733((*S_73064).F, Buf_73065, Buflen_73066);
break;
}
framePtr = framePtr->prev;
}
N_NIMCALL(NimStringDesc*, Llstreamreadall_73051)(TY73013* S_73053) {
NimStringDesc* Result_73371;
NI Bytes_73373;
NI I_73374;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "LLStreamReadAll";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_73371 = 0;
Bytes_73373 = 0;
I_73374 = 0;
F.line = 180;F.filename = "llstream.nim";
switch ((*S_73053).Kind) {
case ((NU8) 0):
case ((NU8) 3):
F.line = 182;F.filename = "llstream.nim";
Result_73371 = copyString(((NimStringDesc*) &TMP73174));
break;
case ((NU8) 1):
F.line = 184;F.filename = "llstream.nim";
if (!((*S_73053).Rd == 0)) goto LA2;
F.line = 184;F.filename = "llstream.nim";
Result_73371 = copyString((*S_73053).S);
goto LA1;
LA2: ;
F.line = 185;F.filename = "llstream.nim";
Result_73371 = copyStr((*S_73053).S, addInt((*S_73053).Rd, 0));
LA1: ;
F.line = 186;F.filename = "llstream.nim";
(*S_73053).Rd = (*S_73053).S->Sup.len;
break;
case ((NU8) 2):
F.line = 188;F.filename = "llstream.nim";
Result_73371 = mnewString(2048);
F.line = 189;F.filename = "llstream.nim";
if ((NU)(0) > (NU)(Result_73371->Sup.len)) raiseIndexError();
Bytes_73373 = Readbuffer_3714((*S_73053).F, ((void*) (&Result_73371->data[0])), 2048);
F.line = 190;F.filename = "llstream.nim";
I_73374 = Bytes_73373;
F.line = 191;F.filename = "llstream.nim";
while (1) {
if (!(Bytes_73373 == 2048)) goto LA4;
F.line = 192;F.filename = "llstream.nim";
Result_73371 = setLengthStr(Result_73371, addInt(I_73374, 2048));
F.line = 193;F.filename = "llstream.nim";
if ((NU)(addInt(I_73374, 0)) > (NU)(Result_73371->Sup.len)) raiseIndexError();
Bytes_73373 = Readbuffer_3714((*S_73053).F, ((void*) (&Result_73371->data[addInt(I_73374, 0)])), 2048);
F.line = 194;F.filename = "llstream.nim";
I_73374 = addInt(I_73374, Bytes_73373);
} LA4: ;
F.line = 195;F.filename = "llstream.nim";
Result_73371 = setLengthStr(Result_73371, I_73374);
break;
}
framePtr = framePtr->prev;
return Result_73371;
}
N_NOINLINE(void, llstreamInit)(void) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "llstream";
F.prev = framePtr;
F.filename = "rod/llstream.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
framePtr = framePtr->prev;
}

