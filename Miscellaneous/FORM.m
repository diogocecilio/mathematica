(* ::Package:: *)

ComputeRandomVarData[distribution_,mean_,sdev_]:=Block[{p1,p2,case},
case=distribution;
Switch[case
,"NORMAL",
p1=mean;
p2=sdev;
case=1;
,"LOGNORMAL",
p2=Sqrt[Log[1+(sdev/mean)^2]];
p1=Log[mean ]-0.5 p2^2;
case=2;
,"DETERM",
p2=0;
p1=mean ;
case=3;
,"UNIFORME",
p1=1/2 (1+2 mean-Sqrt[1+12 sdev^2]);
p2=1/2 (-1+2 mean+Sqrt[1+12 sdev^2]);
case=4;
,"WEIBULL MIN",
p1=mean+N[EulerGamma]/p2;
p2= Pi/(Sqrt[6]sdev);
case=5;
];
{mean,sdev,p1,p2,case}
];
PHI[x_]:=CDF[NormalDistribution[0,1],x];
InvPHI[x_]:=InverseCDF[NormalDistribution[0,1],x];
phi[x_]:=PDF[NormalDistribution[0,1],x];
ComputeY[RvVec_,Nsamples_]:=Block[{y,x,nrv,i,j,mu,sig,p1,p2,case},
nrv=Length[RvVec];
y=Table[0,{nrv}];
For[j=1,j<=nrv,j++,
{mu,sig,p1,p2,case}=RvVec[[j]];
y[[j]]=RandomVariate[NormalDistribution[0,1],Nsamples];
];
Transpose[y]
]


MeritFunction[GxGradx_,y_,Jxy_,Mneq_,c_,vvars_]:= Block[{x,val},
val=(y.y)/2+c Abs[GxGradx[vvars,Jxy.y+Mneq][[1]]];
val
];
ComputeC[y_,grady_,dk_,g_]:= Block[{c,eta=2},
If[Abs[g]<10^-8,
c = eta
,
c=eta Abs[1/g y.grady/grady.grady]
];
c
];
(*PenalizeXhalf[x1_,x2_,Xmax_,Xmin_]:=Block[{xpen,Penalized,PenalSteps,sz,a,b,i,counter},
 xpen = x2;
sz=Length[x1];
counter=1;
For[i=1,i<= sz,i++,
While[xpen[[i]]>= Xmax[[i]] && counter<=100,
xpen[[i]] = (x2[[i]]+x1[[i]])/2; 
counter++;
];
counter=1;
While[xpen[[i]]<= Xmin[[i]] && counter<=100,
xpen[[i]] = (x2[[i]]+x1[[i]])/2; 
counter++;
];
];

xpen
];
*)
PenalizeXhalf[x1_,x2_,Xmax_,Xmin_]:=Block[{xpen,NRV},(
xpen = x2;
NRV=Length[x1];
Do[If[xpen[[i]]>= Xmax[[i]],xpen[[i]] = (x2[[i]]+x1[[i]])/2],{i,1,NRV}];
Do[If[xpen[[i]]<=  Xmin[[i]],xpen[[i]] = (x2[[i]]+x1[[i]])/2],{i,1,NRV}];

Return[xpen];
)];
ComputeExtremes[RandonVar_]:=Block[{xmax,xmin,mu,sig,p1,p2,case },
{mu,sig,p1,p2,case}=RandonVar;

If[case!=4,(*se for diferente de uniforme*)
xmax=mu+ 3 sig mu;
xmin=mu- 3 sig mu;
,
xmin=p1;
xmax=p2;
];
{xmax,xmin}
];
ArmijoLineSearch[GxGradx_,y_,grady_,Jxy_,Mneq_,dk_,kprev_,vvars_]:=Block[{grad,gx,c,kk,My,a=0.1,b=0.5,k,kmax=30,gradMtimesD,A,BB,B,gy,an,an1,tolerance=10^-5},
k=kprev;

{gy,grad}=GxGradx[vvars,y];
{gx,grad}=GxGradx[vvars,Jxy.y+Mneq];
c=ComputeC[y,grady,dk,gx];
gradMtimesD = (y+c Sign[gy]grady).dk;
My = MeritFunction[GxGradx,y,Jxy,Mneq,c,vvars];
A=MeritFunction[GxGradx,y+b^k dk ,Jxy,Mneq,c,vvars];
B=My+a b^k gradMtimesD;
While[k<=kmax&&A>B,
A=MeritFunction[GxGradx,y+b^k dk ,Jxy,Mneq,c,vvars];
B=My+a b^k gradMtimesD;
k++;
];
If[k>=kmax, 
Return[{-2,1}];
,
Return[{k,b^k}];
];
];


FromYtoZ[y_,Rx_]:=Block[{x,sz,i,j,var,z,Jyz,Jzy},
sz=Length[y];
{Jzy,Jyz} = ComputeJYZ[Rx];
z=Table[0,{sz}];
For[j=1,j<=sz,j++,
z[[j]]=Jyz.y[[j]];
];
z
];
F[RandonVar_,x_]:=Block[{fx,mu,sig,p1,p2,case,Fx},
{mu,sig,p1,p2,case}=RandonVar;
Switch[case
,1,(*Normal*)
Fx=CDF[NormalDistribution[mu,sig],x];
,2,(*LogNormal*)
Fx=CDF[LogNormalDistribution[mu,sig],x];
,3,(*Deterministico*)
Fx=If[x>= p1,1.0,0];
,4,(*Uniforme*)
Fx=CDF[UniformDistribution[{p1,p2}],x];
(*Fx=If[x\[GreaterEqual] p2,1.0,If[x\[LessEqual] p1,0.0,(x-p1)/(p2-p1)]];*)
,5,

];
Fx
];
f[RandonVar_,x_]:=Block[{fx,mu,sig,p1,p2,case},
{mu,sig,p1,p2,case}=RandonVar;
Switch[case
,1,(*Normal*)
fx=PDF[NormalDistribution[mu,sig],x];
,2,(*LogNormal*)
fx=PDF[LogNormalDistribution[mu,sig],x];
,3,(*Deterministico*)
fx=If[x>= 1.05 p1,0.0,If[x<= 0.95 p1,0.0,10]];
,4,(*Uniforme*)
fx=PDF[UniformDistribution[{p1,p2}],x];
,5,
fx=PDF[WeibullDistribution[p1,p2],x];
];
fx
];

(*zi=INVFIE[StCDF[RV[[i]],xi[[i]]]];
Dneq[[i]] = fi[zi]/StPDF[RV[[i]],xi[[i]]];
Mneq[[i]] = xi[[i]] - zi*Dneq[[i]];*)
ComputeXZ[RandonVar_,x_]:=Block[{mu,sig,z,SdevNeq,case,MuNeq,p1,p2},
{mu,sig,p1,p2,case}=RandonVar;
Switch[case
,1,(*Normal*)
SdevNeq=sig;
MuNeq=mu;
,2,(*LogNormal*)
SdevNeq=x p2;
MuNeq=x*(1-Log[x]+p1);
,3,(*Deterministico*)
SdevNeq=1;
MuNeq=mu;
,4,(*Uniforme*)
z=InvPHI[F[RandonVar,x]];
SdevNeq=phi[z]/f[RandonVar,x];
MuNeq=x-z SdevNeq;
,5,(*Geral*)
z=InverseCDF[WeibullDistribution[p1,p2],x];
z=p3+(p1-p3)*(-Log[1-WeibullDistribution[p1,p2]])^(1/p2);
SdevNeq=phi[z]/f[RandonVar,x];
MuNeq=x-z SdevNeq;
];
{SdevNeq,MuNeq}
];
ComputeJXZ[RandonVarVec_,x_]:=Block[{sz,i,j,JXZ,JZX,MuNeq,SdevNeq,MuNeqEquiv,Mean},
sz=Length[RandonVarVec];
JXZ=Table[0,{sz},{sz}];
JZX=Table[0,{sz},{sz}];
MuNeqEquiv=Table[0,{sz}];
Mean=Table[0,{sz}];
For[i=1,i<=sz,i++,
{SdevNeq,MuNeq}=ComputeXZ[RandonVarVec[[i]],x[[i]]];
JXZ[[i,i]]=SdevNeq;
JZX[[i,i]]=1/SdevNeq;
MuNeqEquiv[[i]]=MuNeq;
];
{JXZ,JZX,MuNeqEquiv}
];
ComputeJYZ[RX_]:=Block[{cx,L,correlated,Jyz,Jzy,NRV},
NRV=Length[RX];
If[Det[RX]!=1,
L=Transpose[CholeskyDecomposition[RX]];
Jyz=Inverse[L];
Jzy=L;
If[Det[(L.Transpose[L])-RX]> 10^-8,Print["Attention, Cholesky decomposition failed!"]];
,
Jyz=IdentityMatrix[NRV];
Jzy=IdentityMatrix[NRV];
];
Return[{Jyz,Jzy}];
];
ComputeExtremes[RandonVar_]:=Block[{xmax,xmin,mu,sig,p1,p2,case },
{mu,sig,p1,p2,case}=RandonVar;

If[case!=4,(*se for diferente de uniforme*)
xmax=mu+3sig mu;
xmin=mu- 3 sig mu;
,
xmin=p1;
xmax=p2;
];
{xmax,xmin}
];
FromXtoY[RvVec_,x_,Jyz_,Jzy_]:=Block[{Jzx,Jxz,Jxy,Jyx,Mneq,y},
{Jxz,Jzx,Mneq} =  ComputeJXZ[RvVec,x];
Jyx = Jzy.Jzx;
Jxy = Jxz.Jyz;
y=Jyx.(x-Mneq);
{y,Jxy,Mneq}
];
FromYtoX[RvVec_,y_,Rx_]:=Block[{Jzx,Jxz,Jxy,Jyx,Mneq,x,Jyz,Jzy},
{Jyz,Jzy} =ComputeJYZ[Rx];
{Jxz,Jzx,Mneq} =  ComputeJXZ[RvVec,x];
Jyx = Jzy.Jzx;
Jxy = Jxz.Jyz;
x=Jxy.y+Mneq;
{x,Jyx,Mneq}
];
FromZtoX[RvVec_,z_]:=Block[{x,sz,i,j,JXZ,JZX,MuNeqEquiv,rv,nrv,mu,sig,p1,p2,case,Fx,fx,hx},
sz=Length[z];
nrv=Length[RvVec];
x=Table[0,{sz},{nrv}];
fx=Table[0,{sz},{nrv}];
hx=Table[0,{sz},{nrv}];
For[j=1,j<=sz,j++,
For[i=1,i<=nrv,i++,
{mu,sig,p1,p2,case}=RvVec[[i]];
If[case==1,
x[[j,i]]=z[[j,i]] p2+p1 ;
];
If[case==2,
x[[j,i]]=Exp[z[[j,i]] p2+p1];
];
If[case==3,
x[[j,i]]=z[[j,i]]p1;
];
If[case==4,
Fx=CDF[UniformDistribution[{p1,p2}],z[[j,i]]];
x[[j,i]]=(p2-p1)*Fx+p1;
];
If[case!=1 && case!=2 && case!=4 && case!=3,
Print["Error Distribution not Implemented!"];
];
fx[[j,i]]=f[RvVec[[i]],x[[j,i]]];
hx[[j,i]]=phi[x[[j,i]]];
];
];
{x,fx,hx}
];
F[RandonVar_,x_]:=Block[{fx,mu,sig,p1,p2,case,Fx},
{mu,sig,p1,p2,case}=RandonVar;
Switch[case
,1,(*Normal*)
Fx=CDF[NormalDistribution[mu,sig],x];
,2,(*LogNormal*)
Fx=CDF[LogNormalDistribution[mu,sig],x];
,3,(*Deterministico*)
Fx=If[x>= p1,1.0,0];
,4,(*Uniforme*)
Fx=CDF[UniformDistribution[{p1,p2}],x];
(*Fx=If[x\[GreaterEqual] p2,1.0,If[x\[LessEqual] p1,0.0,(x-p1)/(p2-p1)]];*)
];
Fx
];
HRLF[RvVec_,Rx_,GxGradx_,Vars_]:=Block[{yy={},gg={},vbeta={},grad,guess,vvars=Vars,i,y0,Mneq,x,y,g,gradx,grady,betan,betan1,k,checkconv=1,tol=0.001,NmaxIT=100,Jyz,Jzy,Jzx,Jxz,Jxy,Jyx,alpha,xn,xmax,xmin,nrv,PostProcess={},post=False,Sdev,DistribCases,Mean},
k=1;
Mean=Transpose[RvVec][[1]];
x=Mean;
Sdev=Transpose[RvVec][[2]];
DistribCases=Transpose[RvVec][[5]];
nrv=Length[RvVec];
xmax=Table[0,{nrv}];
xmin=Table[0,{nrv}];
For[i=1,i<=nrv,i++,
{xmax[[i]],xmin[[i]]}=ComputeExtremes[RvVec[[i]]];
];
{Jzy,Jyz}  = ComputeJYZ[Rx];
{y,Jxy,Mneq}=FromXtoY[RvVec,x,Jyz,Jzy];
{g,grad}=GxGradx[vvars,Mean];

k=1;
betan=0;
While[checkconv>tol &&k< NmaxIT,
(*Print[ " | iter = ",k,"  | residual = ",checkconv," | G(x) = ",N[g], "  | y = ",y ];*)
grady=Transpose[Jxy].grad;
y=((grady.y)-g)/(grady.grady) grady;
x=Jxy.y+Mneq;
If[post==True,
AppendTo[PostProcess,x];
];
{y,Jxy,Mneq}=FromXtoY[RvVec,x,Jyz,Jzy];
{g,grad}=GxGradx[vvars,x];
betan1=Sqrt[y.y];

checkconv=Abs[betan1-betan];
(*AppendTo[yy,y];
AppendTo[gg,g];
AppendTo[vbeta,betan1];*)
(*checkconv=Abs[g];*)
betan=betan1;
k++;
];
(*Print[ " | iter = ",k,"  | residual = ",checkconv," | G(x) = ",N[g], "  | y = ",y ];*)

alpha=( grady/Sqrt[grady.grady])^2;
(*Print[ " | iter = ",k,"  | residual = ",checkconv," | G(x) = ",g ,"| Beta = ", betan];*)
(*Print[ "y = ",y];*)
{betan,PHI[-betan],y,alpha}
];
iHRLF[RvVec_,Rx_,GxGradx_,Vars_]:=Block[{vvars=Vars,grad,i,y0,Mneq,x,y,g,gradx,grady,betan,betan1,k,checkconv=1,tol=10^-3,NmaxIT=100,Jyz,Jzy,Jzx,Jxz,Jxy,Jyx,alfa,dk,c,sensivity,kn,kn1,post=False,PostProcess,xn,xmax,xmin,nrv,Sdev,DistribCases,Mean},
k=1;
Mean=Transpose[RvVec][[1]];
x=Mean;
Sdev=Transpose[RvVec][[2]];
DistribCases=Transpose[RvVec][[5]];
nrv=Length[RvVec];
xmax=Table[0,{nrv}];
xmin=Table[0,{nrv}];
For[i=1,i<=nrv,i++,
{xmax[[i]],xmin[[i]]}=ComputeExtremes[RvVec[[i]]];
];
{Jzy,Jyz}  = ComputeJYZ[Rx];
{y,Jxy,Mneq}=FromXtoY[RvVec,x,Jyz,Jzy];
{g,grad}=GxGradx[vvars,x];
k=1;
betan=0;
alfa=1;
kn=0;
kn1=0;
alfa=1;
If[post==True,
PostProcess={};
];
xn=x;
(*Print["x0 = ",xn];*)
While[checkconv>tol &&k< NmaxIT,
(*Print[ " | iter = ",k,"  | residual = ",checkconv," | G(x) = ",N[g] ," | alfa = ",alfa, "| kn = ",kn];*)
grady=Transpose[Jxy].grad;
dk=(((grady.y)-g)/(grady.grady) grady)-y;
{kn1,alfa}=ArmijoLineSearch[GxGradx,y,grady,Jxy,Mneq,dk,kn,vvars];
kn=kn1;
y+=alfa dk;
xn=Jxy.y+Mneq;
x=PenalizeXhalf[x,xn,xmax,xmin];
(*Print["*****"];
xn=Jxy.y+Mneq;
Print["xmin = ",xmin, " xmax = ",xmax, " x = ",x , " xn = ",xn];
x=PenalizeXhalf[x,xn,xmin,xmax];
Print["xmin = ",xmin, " xmax = ",xmax, " x = ",x , " xn = ",xn];*)
If[post==True,
AppendTo[PostProcess,x];
];
{y,Jxy,Mneq}=FromXtoY[RvVec,x,Jyz,Jzy];
{g,grad}=GxGradx[vvars,x];
betan1=Norm[y];
(*checkconv=Abs[betan1-betan];*)
checkconv=Abs[g];
betan=betan1;
k++;
];
Print[ " | iter = ",k,"  | residual = ",checkconv," | G(x) = ",g ," | alfa = ",alfa, "| kn = ",kn, "| Beta = ", betan];
sensivity=( grady/Sqrt[grady.grady])^2;
(*Print[" SOLUTION "];
Print[" x = ",x];
Print[" \[Beta] = ",betan];
Print[ " Pf = ",PHI[-betan] ];
Print[TableForm[{{" Y "," sensivity "},{y,sensivity}}]];*)
{betan,PHI[-betan],sensivity,PostProcess}
];


MonteCarlo[RvVec_,Rx_,GxGradx_,Vars_,Nsamples_]:=Block[{y,z,x,counter,Pf,beta,i,PostProc,xfailed={},fx,hx,vartemp},
y=ComputeY[RvVec,Nsamples];
z=FromYtoZ[y,Rx];
{x,fx,hx}=FromZtoX[RvVec,z];

PostProc=Table[0,{Nsamples},{2}];
counter=0;
vartemp=0;
For[i=1,i<=Nsamples,i++,
(*Print["fx = ",fx[[i]]];
Print["hx = ",hx[[i]]];
Print["hx/fx = ",hx[[i]]/fx[[i]]];*)
If[GxGradx[Vars,x[[i]]][[1]]<=0,
(*vartemp=fx[[i]]/hx[[i]];*)
AppendTo[xfailed,x[[i]]];
counter++;
];

(*PostProc[[i,1]]=i;
beta=-InvPHI[N[counter/Nsamples]];
PostProc[[i,2]]=beta;*)
];
Print["Counter = ",counter];
Pf=N[counter/Nsamples];
beta=-InvPHI[N[counter/Nsamples]];
Print["Pf Crude Monte Carlo  = ",Pf];
Print["\[Beta] Crude Monte Carlo = ",beta];
(*{PostProc,x,xfailed,beta}*)
];

MonteCarloII[RvVec_,Rx_,Gx_,Vars_,Nsamples_]:=Block[{y,z,x,counter,Pf,beta,i,PostProc,xfailed={},fx,hx,vartemp},
y=ComputeY[RvVec,Nsamples];
z=FromYtoZ[y,Rx];
{x,fx,hx}=FromZtoX[RvVec,z];

PostProc=Table[0,{Nsamples},{2}];
counter=0;
vartemp=0;
For[i=1,i<=Nsamples,i++,
(*Print["fx = ",fx[[i]]];
Print["hx = ",hx[[i]]];
Print["hx/fx = ",hx[[i]]/fx[[i]]];*)
If[Gx[Vars,x[[i]]][[1]]<=0,
(*vartemp=fx[[i]]/hx[[i]];*)
AppendTo[xfailed,x[[i]]];
counter++;
];

(*PostProc[[i,1]]=i;
beta=-InvPHI[N[counter/Nsamples]];
PostProc[[i,2]]=beta;*)
];
Print["Counter = ",counter];
Pf=N[counter/Nsamples];
beta=-InvPHI[N[counter/Nsamples]];
Print["Pf Crude Monte Carlo  = ",Pf];
Print["\[Beta] Crude Monte Carlo = ",beta];
(*{PostProc,x,xfailed,beta}*)
];

ComputeSamples[RvVec_,Nsamples_]:=Block[{y,x,nrv,i,j,mu,sig,p1,p2,case,stddev,beta},
nrv=Length[RvVec];
y=Table[0,{nrv}];
For[j=1,j<=nrv,j++,
y[[j]]=RandomVariate[NormalDistribution[0,1],Nsamples];
];
Transpose[y]
]


MonteCarloIS[RvVec_,Rx_,GxGradx_,Vars_,Nsamples_]:=Block[{n,u,internalvars,mu,sig,p1,p2,case,w,,nrv,j,f,h,DesignPoint,ISweight,pfsum,pf,y,z,x,counter,Pf,beta,i,PostProc,xfailed={},fx,hx,vartemp},

{beta,pf,DesignPoint}=HRLF[RvVec,Rx,GxGradx,Vars];

y=ComputeSamples[RvVec,Nsamples];
z=FromYtoZ[y,Rx];
{x,fx,hx}=FromZtoX[RvVec,z];


mu=0;
sig=1;
p1=1/2 (1+2 mu-Sqrt[1+12 sig^2]);
p2=1/2 (-1+2 mu+Sqrt[1+12 sig^2]);
n=Nsamples;
nrv=Length[RvVec];
x=Table[0,{nrv}];


For[j=1,j<=nrv,j++,
{mu,sig,p1,p2,case}=RvVec[[j]];
x[[j]]=RandomVariate[NormalDistribution[mu,sig],n];
];


f=Table[0,{nrv}];
w=Table[0,{Nsamples},{nrv}];
hh=Table[0,{Nsamples}];

(*Print[w//MatrixForm]*)
Print["u = ",u];
Print["x = ",x];
Print["RvVec = ",RvVec];

(*X1 =  KTRANDOM VAR | X2 SIGY | X3 t | X4 ov | X5 ex | X6 rs | X7 Nax | X8 Pint | X9 Pext *)

For[i=1,i<=Nsamples,i++,

For[j=1,j<=nrv,j++,

{mu,sig,p1,p2,case}=RvVec[[j]];
(*Print["RvVec[[j]] ",RvVec[[j]]];*)
(*Print["x[[j,i]] ",x[[j,i]]];*)
f=PDF[UniformDistribution[{mu-3 sig ,mu+3 sig}],x[[j,i]]];
h=PDF[NormalDistribution[DesignPoint[[j]],1],x[[j,i]]];
Print["f ",f];
w[[i,j]]=f/h;
];
];


Print["h = ",h//MatrixForm];
Print["f = ",f//MatrixForm];
Print["f/h = ",f/h//MatrixForm];
Print["w= ",w//Chop];


PostProc=Table[0,{Nsamples},{2}];
counter=0;
vartemp=0;
For[i=1,i<=Nsamples,i++,


If[GxGradx[Vars,x[[i]]][[1]]<=0,
AppendTo[xfailed,x[[i]]];
counter++;
];

];

beta=-InvPHI[N[counter/Nsamples]];
Print["Counter = ",counter];
Pf=N[counter/Nsamples];
Print["Pf Crude Monte Carlo  = ",Pf];
Print["\[Beta] Crude Monte Carlo = ",beta];
];

ComputeBeta[DeterministicData_,RandomVarsData_,Grad_,type_,print_]:=Block[{x,area,solution={},vars,i,betan,prob,alpha,PostProcess,k,g,RVVec,RX,PiData,PeData,ax,pipedatavec,de,di,young,nu,weightperfeet,L0,LF,sigy},
{RVVec,RX}=RandomVarsData;
{PiData,PeData,ax,pipedatavec}=DeterministicData;
{de,di,young,nu,weightperfeet,L0,LF,sigy}=pipedatavec;
area=Pi/4(de^2-di^2);
For[i=1,i<=Length[PiData],i++,

If[type=="colapso",
vars={ax[[i,1]]/area,sigy,PiData[[i,1]],PeData[[i,1]],de,de-di,young,nu};
,
vars={0.104,de,de-di,sigy 1.15,ax[[i,1]]/area,PiData[[i,1]],PeData[[i,1]]};
];
{betan,prob,alpha,PostProcess,k,g,x}=HRLF[RVVec,RX,Grad,vars];
If[print==True,
Print["beta = ",betan];
Print["PHI[-beta] = ",prob];
Print["alfa = ",alpha ];
Print["k = ", k ];
Print["G[x] = ", g];
Print[ "X = ", x];
];
AppendTo[solution,{betan,-PiData[[i,2]]}];
];
solution
]

FromYtoX[RvVec_,y_,Rx_]:=Block[{Jzx,Jxz,Jxy,Jyx,Mneq,x,Jyz,Jzy},
{Jyz,Jzy} =ComputeJYZ[Rx];
{Jxz,Jzx,Mneq} =  ComputeJXZ[RvVec,x];
Jyx = Jzy.Jzx;
Jxy = Jxz.Jyz;
x=Jxy.y+Mneq;
{x,Jyx,Mneq}
];
FindDesignPoint[RvVec_,Rx_,GxGradx_,Vars_]:=Block[{beta,vvars=Vars,Jxy,Jzy,Jyz,grad,Jyx,Mneq,NmaxIT=60,MEAN,x,y,g,gradx,grady,vbeta,k,CONVERGENCE,alfa,fopf,NegativeBeta},( 

k=1;

MEAN=Transpose[RvVec][[1]];
x=MEAN;
{Jzy,Jyz}  = ComputeJYZ[Rx];
{y,Jxy,Mneq}=FromXtoY[RvVec,x,Jyz,Jzy];

{g,grad}=GxGradx[vvars,x];

CONVERGENCE = False;

While[((Abs[g]>10^-3)&&(k< NmaxIT)),

{g,gradx}=GxGradx[vvars,x];
grady=Transpose[Jxy].gradx;

y=(grady.y-g)/grady.grady grady;

x=Jxy.y+Mneq;

{y,Jxy,Mneq}=FromXtoY[RvVec,x,Jyz,Jzy];

(*If[GAUSSIAN==False,
x[[k+1]] = PENALIZEXHALF[x[[k]],x[[k+1]]];
{Jxz,Jzx} = JacobXZ[RVX,x[[k+1]]];
Jyx = Jyz.Jzx;
Jxy = Jxz.Jzy;
y[[k+1]]=Jyx.(x[[k+1]]-Mneq);
];*)

{g,gradx}=GxGradx[vvars,x];

vbeta=Sqrt[y.y];

k = k+1;

];

alfa =( grady/Sqrt[grady.grady])^2;
beta = vbeta;
Print[ " | iter = ",k , "| G(x)= "  ,g , " | alpha = ",alfa," | Beta = ", beta];
{beta,PHI[-beta],y}
)]

