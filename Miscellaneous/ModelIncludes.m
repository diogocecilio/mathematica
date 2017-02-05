(* ::Package:: *)

MakeCompatibleSizeVectors[refinedvec_,coarsevecl_,coarsevecvar_]:=Block[{newvec,y0,y1,x0,x1,counter,i},
newvec={};
counter=1;
If[Length[coarsevecl]!=Length[coarsevecvar],
Print["N\[ATilde]o \[EAcute] poss\[IAcute]vel realizar o refinamento, os vetores coarse devem ter o mesmo tamanho."];
];
For[i=1,i<Length[coarsevecl],i++,
(*If[i>=Length[coarsevecvar],Break[]];*)
y0=coarsevecvar[[i]];
y1=coarsevecvar[[i+1]];
x0=coarsevecl[[i]];
x1=coarsevecl[[i+1]];
While[(coarsevecl[[i]]<=refinedvec[[counter]]<=coarsevecl[[i+1]])&&counter<Length[refinedvec],
AppendTo[newvec,N[(y1-y0)/(x1-x0) (refinedvec[[counter]]-x0)+y0]];
counter++;
];
If[i==Length[coarsevecl]-1,AppendTo[newvec,N[(y1-y0)/(x1-x0) (refinedvec[[counter]]-x0)+y0]]];
];
newvec//N
]


(* ::Input:: *)
(*17500-14800*)


(*C\[AAcute]lculo da resist\[EHat]ncia ao colapso Klever-Tamano, segundo ISO 10400*)
Hfunc[ov_,ec_,rs_,fy_]:=Max[0,0.127 ov+0.0039ec+0.440 rs/fy];
Hfunc[ov_,ec_,rs_]:=Max[0,0.127 ov+0.0039ec-0.440 rs];
ComputeColapseStrengthKT[siga_,sigy_,pi_,d_,t_,young_,nu_,ov_,ec_,rs_]:=Block[{Po,feff,i,initialguess,min,tabguess,MisesEq,ke=0.825,sol,H,deltapec,deltapy,deltapmises,deltaptresca,ky=0.855,eq,po,Fa,Feff,Fy,Ai,Ao,As,kdr,BurstStrength, ColapseStrength,pyc,pec,pym,xi,Si,dt,c,val},

deltaptresca=ky 2 sigy t/(d-t);

Ai=Pi/4 (d-2t)^2;
Ao=Pi/4 d^2;
As=Ao-Ai;
feff=siga As -pi Ai+po Ao;
(*feff=siga As ;*)
MisesEq=Sqrt[Abs[(ky(4./Sqrt[3.])sigy t/(d-t))^2 (1.-(feff/(ky sigy As))^2)]]-po+pi;

(*initialguess=pi+deltaptresca;*)

tabguess=Table[{i,MisesEq/.po->i},{i,-30000,30000,1000}];
min=Min[Transpose[Abs[tabguess]][[2]]];
initialguess=0.;
For[i=1,i<=Length[tabguess],i++,If[Abs[tabguess[[i,2]]]==min,initialguess=tabguess[[i,1]]]];

Po=FindRoot[MisesEq,{po,initialguess},MaxIterations->100][[1,2]];

deltapmises=Po-pi;

If[deltapmises>deltaptresca,deltapy=(deltapmises+deltaptresca)/2,deltapy=deltapmises];

deltapec=ke (2. young)/(1.-nu^2) 1./((d/t)(d/t-1.)^2);
(*H=Hfunc[ov,ec,rs];*)
H=Hfunc[ov,ec,rs];
ColapseStrength=pi+(2. deltapy deltapec)/(deltapy+deltapec+Sqrt[(deltapy-deltapec)^2 +4. H deltapy deltapec]);
(*Print["ColapseStrength = ",ColapseStrength];*)
ColapseStrength

]


(*C\[AAcute]lculo num\[EAcute]rico de GX e GRADGX de Klever-Tamano*)
ComputeNumericalGradKT[Vars_,Xvec_]:=Block[{vars,guess,dx=0.0001,xvecn,xvecn1,dgdx,derivative,i,X1,X2,X3,X4,X5,X6,X7,X8,X9,NofD,nYieldStrength,PintofD,PextofD,nDe,nt,nYoung,nNu},

{NofD,nYieldStrength,PintofD,PextofD,nDe,nt,nYoung,nNu}=Vars;

(*KTRandomVarsData={{"KTme","NORMAL",0.9991,0.067*0.9991},{"YieldStress","NORMAL",1.1,0.0422*1.1},{"Thickness","NORMAL",1.0069,0.0259*1.0069},{"Ovality","NORMAL",0.217,0.541*0.217},{"Excent","NORMAL",3.924,0.661*3.924},{"Resid. Stress","NORMAL",-0.237,0.332*0.237},{"Nax","NORMAL",1.`,0.01`},{"Pint","NORMAL",1.`,0.01`},{"Pext","NORMAL",1.`,0.01`}}*)

Gx[xvec_]:=xvec[[1]]*ComputeColapseStrengthKT[NofD*xvec[[7]],nYieldStrength*xvec[[2]],PintofD*xvec[[8]],nDe,nt*xvec[[3]],nYoung,nNu,xvec[[4]],xvec[[5]],xvec[[6]]]-(PextofD*xvec[[9]]-PintofD*xvec[[8]]);
xvecn=Xvec;
derivative=Table[0,{Length[xvecn]}];
For[i=1,i<=Length[xvecn],i++,
xvecn1=xvecn;
xvecn1[[i]]+=dx;
dgdx=(Gx[xvecn1]-Gx[xvecn])/dx;
derivative[[i]]=dgdx;
];
{Gx[xvecn],derivative}(*/.{NofD\[Rule]Vars[[1]],nYieldStrength\[Rule]Vars[[2]],PintofD\[Rule]Vars[[3]],PextofD\[Rule]Vars[[4]],nDe\[Rule]Vars[[5]],nt\[Rule]Vars[[6]],nYoung\[Rule]Vars[[7]],nNu\[Rule]Vars[[8]]}*)
]


(*C\[AAcute]lculo da resist\[EHat]ncia \[AGrave] Ruptura de Klever-Stewart*)
ComputeBurstResistance[de_,t_,fu_,sa_,po_]:=Block[{n,a,kdr,kr,puts,pref,Futs,pfactor,pfactorNeck,pM,pBurstKS,pburst},
n=0.1693-fu  8.12 10^-7;
kdr=0.5^(n+1)+(1/Sqrt[3])^(n+1);
kr=(4^(1-n)-1)*3^(n-1);
puts=(2 kdr t fu)/(de- t);
pref=(0.5^n*puts)/2 (((2/Sqrt[3])^(n+1))+1);
Futs=Pi t  fu(de-t);
pfactor=Sqrt[1-kr*(sa/fu)^2];
If[Abs[sa]<fu,a=(1-sa^2/fu^2)/(-3^(1-n)+4^(1-n)),a=0];
(*a=(1-sa^2/fu^2)/(-3^(1-n)+4^(1-n));*)
pfactorNeck=Sqrt[a];
pM=pref pfactor;
pBurstKS=po+Min[pM,(pM+0.5^n puts)/2];
pBurstKS=Min[pM,(pM+0.5^n puts)/2];
If[sa/fu<= (Sqrt[3]/2)^(1-n),
If[pM<= (pM+0.5^n puts)/2,
pburst=po+pM;
pburst=pM;
,
pburst= po+(pM+0.5^n puts)/2;
pburst= (pM+0.5^n puts)/2;
],
pburst=po+pref*pfactorNeck;
pburst=pref*pfactorNeck;
];
pburst//N
];


ComputeDuctileRupture[de_,t_,sigy_,sa_,po_,pi_]:=Block[{feff,kn,ka,area,di,kwall,an,kdr,n,fumn,piR,Fa,Futs,puts,prefM,prefT,kr,eqpm,pM,Feff,sol},
ka=1;
n=0.1693 -sigy  8.12 10^-7;
kn=(4^(1-n) -3^(1-n) );
di=de-2t;
area=Pi/4(de^2 -di^2);
kwall=0.875;
an= 0.05 t;
kdr=(1/2)^(n+1) +(1/Sqrt[3])^(n+1);
fumn=sigy 1.13636;
(*piR=2 kdr fumn (kwall t-ka an)/(de-(kwall t-ka an))*)
(*piRa[pM_]:=po+Min[0.5(pM+prefT),pM];*)
Fa=sa Pi t (de-t);
Futs=Pi t (de-t) fumn;
puts=2 fumn (kwall t-ka an)/(de-(kwall t-ka an));
prefM=(2/Sqrt[3])^(1+n) (1/2)^n puts;
prefT=0.5^n puts;
kr=(4^(1-n)-1)/(3^(1-n));
Feff[pM_]:=((Fa+po  Pi t(de-t)-pM t (de-t)/((kwall t - ka an)(de-kwall t+ka an)) Pi/4 (de-2(kwall t-ka an))^2));
eqpm=pM-(prefM Sqrt[(1-kr (Feff[pM]/Futs)^2)]);
sol=FindRoot[eqpm,{pM,prefM}];



If[Feff[sol[[1,2]]]/Futs<=(Sqrt[3]/2)^(1-n),
(*Ductile rupture*)
Return[(po+Min[0.5(pM+prefT),pM])/.pM->sol[[1,2]]];
];

If[(pi-po)/prefM <=0.5^(1-n),
(*Ductile necking combined loads*)
feff=Futs Sqrt[(1-kn (pi-po)/prefM)^2];
pM=prefM Sqrt[(1-kr (feff/Futs)^2)];
(*Print["Here"];*)
Return[(po+Min[0.5(pM+prefT),pM])];
,

Return[2 kdr fumn (kwall t-ka an)/(de-(kwall t-ka an))];
];


]


(*C\[AAcute]lculo num\[EAcute]rico de GX e GRADGX de Klever-Stewart*)
ComputeNumericalGradKS[Vars_,Xvec_]:=Block[{de,t,fu,sa,pi,po,i,derivative,xvecn1,dgdx,dx=0.0001,xvecn,NofD,x7,nYieldStrength,x3,PintofD,x8,nDe,nt,x2,nYoung,nNu,x4,x5,x6,x1,PextofD,x9,gx,grad,subst},
{de,t,fu,sa,pi,po}=Vars;
xvecn=Xvec;

(*KTRandomVarsData={{"KTme","NORMAL",0.9991,0.067*0.9991},{"YieldStress","NORMAL",1.1,0.0422*1.1},{"Thickness","NORMAL",1.0069,0.0259*1.0069},{"Ovality","NORMAL",0.217,0.541*0.217},{"Excent","NORMAL",3.924,0.661*3.924},{"Resid. Stress","NORMAL",-0.237,0.332*0.237},{"Nax","NORMAL",1.`,0.01`},{"Pint","NORMAL",1.`,0.01`},{"Pext","NORMAL",1.`,0.01`}}*)

(*Gx[xvec_]:= xvec[[1]]*ComputeBurstResistance[de,xvec[[3]]*t,xvec[[2]]*fu,xvec[[4]]*sa,xvec[[5]]*po]-(xvec[[6]] pi-xvec[[5]]*po);*)
Gx[xvec_]:= (xvec[[1]])*ComputeDuctileRupture[de,xvec[[3]]*t,xvec[[2]]*fu,xvec[[4]]*sa,xvec[[5]]*po,pi xvec[[6]]]-(xvec[[6]] pi-xvec[[5]]*po);
derivative=Table[0,{Length[xvecn]}];

For[i=1,i<=Length[xvecn],i++,
xvecn1=xvecn;
xvecn1[[i]]+=dx;
dgdx=(Gx[xvecn1]-Gx[xvecn])/dx;
derivative[[i]]=dgdx;
];
{Gx[xvecn],derivative}
]


(*C\[AAcute]lculo num\[EAcute]rico de GX e GRADGX de Barlow*)
ComputeBurstBarlow[vars_,Xvec_]:=Block[{d,sigy,t,strength,PI,PE,xvecn,derivative,i,xvecn1,dgdx,dx=0.0001},
{d,sigy,t,PI,PE}=vars;
Gx[xvec_]:= 0.875 (2 sigy xvec[[2]])/(d/(t xvec[[3]]))-(PI-PE);
xvecn=Xvec;
derivative=Table[0,{Length[xvecn]}];

For[i=1,i<=Length[xvecn],i++,
xvecn1=xvecn;
xvecn1[[i]]+=dx;
dgdx=(Gx[xvecn1]-Gx[xvecn])/dx;
derivative[[i]]=dgdx;
];
{Gx[xvecn],derivative}
]


(*C\[AAcute]lculo num\[EAcute]rico de GX e GRADGX de Barlow*)
ComputeBurstBarlow[vars_]:=Block[{d,sigy,t,PI,PE},
{d,sigy,t,PI,PE}=vars;
 0.875 2 sigy/(d/t)
]


(* ::Input:: *)
(**)


(*M\[EAcute]todo de verifica\[CCedilla]\[ATilde]o do c\[AAcute]lculo da derivada, conforme descri\[CCedilla]\[ATilde]o acima*)
checkconv[vars_,pt_,GxGradx_]:=Block[{nsz=10,sol,incval,numrows,range,i,estimateresidual,res,diffnorm,k,actualstate,tan,referenceresidual,pts,j,incvalres,resstate},
diffnorm=Table[0,{nsz}];
referenceresidual=GxGradx[vars,pt][[1]];
tan=GxGradx[vars,pt][[2]] ;
numrows=Length[pt];
range=Table[0,{numrows}];
incval=Table[0,{numrows}];
range=pt/197;
For[i=1,i<=numrows,i++,
incval[[i]]= range[[i]] RandomReal[];
];
Print["tan = ",tan];
Print["incval = ",incval];
estimateresidual=tan .incval;
Print["estimateresidual = ",estimateresidual];
For[i=1,i<nsz,i++,
actualstate=pt;
For[k=1,k<=numrows,k++,
actualstate[[k]]+=incval[[k]]*(i/nsz);
];
res=GxGradx[vars,actualstate][[1]];
res-=referenceresidual;
res=res-estimateresidual(i/nsz);
diffnorm[[i]]=Norm[res];
];
For[i=2,i<nsz,i++,
sol=( Log[10., diffnorm[[i]] ]- Log[10.,diffnorm[[i-1]] ] )/( Log[10.,i]-Log[10.,i-1]);
Print[sol];
];
diffnorm
]

ComputePipeStrength[siga_,sigy_,d_,t_,young_,nu_]:=Block[{BurstStrength, ColapseStrength,dt,Ypa,A,B,C,F,G,range1,range2,range3},
BurstStrength=0.875 2 sigy/(d/t);
dt=d/t;
Ypa=sigy (Sqrt[1-3/4 (siga/sigy)^2]-1/2 siga/sigy);
A=2.8762+0.10679 10^-5 Ypa+0.21301 10^-10 Ypa^2-0.53132 10^-16 Ypa^3;
B=0.026233+0.50609 10^-6 Ypa;
C=-465.93+0.030867 Ypa-0.10483 10^-7 Ypa^2+0.36989 10^-13 Ypa^3;
F=(46.95 10^6 ((3(B/A))/(2+B/A))^3)/(Ypa((3(B/A))/(2+B/A)-B/A)(1-(3(B/A))/(2+B/A))^2);
G=F B/A;
range1=(2+B/A)/(3 B/A);
If[dt>= range1,
ColapseStrength=(2 young)/(1-nu^2) 1/(dt (dt-1)^2);
];
range2=(Ypa(A-F))/(C+Ypa(B-G));
If[range2<= dt<= range1,
ColapseStrength= (F/dt-G)Ypa;
];
range3=(Sqrt[(A-2)^2+8(B+C/Ypa)]+(A-2))/(2(B+C/Ypa));
If[(range3<= dt<= range2),
ColapseStrength=Ypa (A/dt-B)-C;
];

If[dt<= range3,
ColapseStrength=2Ypa (dt-1)/dt^2;
];
{BurstStrength,ColapseStrength}
];

(*C\[AAcute]lculo num\[EAcute]rico de GX e GRADGX de Klever-Tamano*)
ComputeNumericalGradAPI[Vars_,Xvec_]:=Block[{vars,guess,dx=0.0001,xvecn,xvecn1,dgdx,derivative,i,X1,X2,X3,X4,X5,X6,X7,X8,X9,NofD,nYieldStrength,PintofD,PextofD,nDe,nt,nYoung,nNu},

(*de,t,sigy,Ffinal[[i]]/area,PIfim[[i]],PEfim[[i]]*)
(*vars=Table[{de,t,sigy,Ffinal[[i]]/area,PIfim[[i]],PEfim[[i]]},{i,1,Length[Ffinal]}];*)
(*{nDe,nt,nYieldStrength,NofD,PintofD,PextofD}=Vars;*)
{NofD,nYieldStrength,PintofD,PextofD,nDe,nt,nYoung,nNu}=Vars;

(*KTRandomVarsData={{"KTme","NORMAL",0.9991,0.067*0.9991},{"YieldStress","NORMAL",1.1,0.0422*1.1},{"Thickness","NORMAL",1.0069,0.0259*1.0069},{"Ovality","NORMAL",0.217,0.541*0.217},{"Excent","NORMAL",3.924,0.661*3.924},{"Resid. Stress","NORMAL",-0.237,0.332*0.237},{"Nax","NORMAL",1.`,0.01`},{"Pint","NORMAL",1.`,0.01`},{"Pext","NORMAL",1.`,0.01`}}*)
(*ComputePipeStrength[siga_,sigy_,d_,t_,young_,nu_]*)
Gx[xvec_]:=(ComputePipeStrength[NofD xvec[[7]],nYieldStrength xvec[[2]],nDe,nt xvec[[3]],nYoung,nNu][[2]])-(PextofD*xvec[[9]]-PintofD*xvec[[8]]);
xvecn=Xvec;
derivative=Table[0,{Length[xvecn]}];
For[i=1,i<=Length[xvecn],i++,
xvecn1=xvecn;
xvecn1[[i]]+=dx;
dgdx=(Gx[xvecn1]-Gx[xvecn])/dx;
derivative[[i]]=dgdx;
];
{Gx[xvecn],derivative}(*/.{NofD\[Rule]Vars[[1]],nYieldStrength\[Rule]Vars[[2]],PintofD\[Rule]Vars[[3]],PextofD\[Rule]Vars[[4]],nDe\[Rule]Vars[[5]],nt\[Rule]Vars[[6]],nYoung\[Rule]Vars[[7]],nNu\[Rule]Vars[[8]]}*)
]
