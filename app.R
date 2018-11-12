#
# This is a Shiny web application. You can run the application by clicking
# the 'Run App' button above.
#
# Find out more about building applications with Shiny here:
#
#    http://shiny.rstudio.com/
#

#!!!! Please install the packages before runing App.
#install.packages("shiny")
#install.packages("imputeYn")
#install.packages("boot")
#install.packages("emplik")
#install.packages("mvtnorm")
#install.packages("msm")
#install.packages("psych")
#install.packages("ggplot2")
#install.packages("stats")
#install.packages("pspline")
#install.packages("ggplot2")
#install.packages("RCurl")
#install.packages("dplyr")

library(shiny)
library(imputeYn)
library(boot)
library(emplik)
library(mvtnorm)
library(msm)
library(psych)
library(ggplot2)
library(stats)
library(pspline)
library(RCurl)
library(dplyr)
#Creating "V" Matrix
vmat<-function(x,ro){
  ns<-length(x)
a<-0
for (i in 1:(ns-1)) {
  a[i]<-exp(-ro*(x[i+1]-x[i]))
}
v<-matrix(0,ns,ns)
for (m1 in 2:(ns-1)) {
  for (m2 in 2:(ns-1)){
    if (m1==m2) {
      v[m1,m2]<-1+(((a[m1-1])^2)/(1-(a[m1-1]^2)))+(((a[m1])^2)/(1-(a[m1]^2)))
    }
    if (m1==m2+1){
      v[m1,m2]<- -a[1]/(1-a[1]^2)
    }
    if (m2==m1+1){
      v[m1,m2]<- -a[1]/(1-a[1]^2)
    }
  }
}
v[1,1]<-1/(1-a[1]^2)
v[ns,ns]<-1/(1-a[ns-1]^2)
return(v)
}
#Hat matrix for SS--------------------------------------------------------------
#SMOOTHING SPLINE METHOD
hatss<-function(x,y){
  ns<-length(x)
  v<-matrix(0,ns,ns)
  v<-vmat(x,0.7)
  h<-0
for (b in 1:ns-1) {
  h[b]<-x[b+1]-x[b]
}
Q<-matrix(0,ns,(ns-2))
for (i in 1:(ns-2)) {
  for (j in 2:ns) {
    if (i==j-1) {
      Q[j-1,i]<-(1/h[j-1])
    }
    if (i==j) {
      Q[j-1,i]<- (-(1/h[j-1])+(1/h[j]))
    }
    if (i==j+1) {
      Q[j-1,i]<-(1/h[j])
    }
    if (abs(i-j)>=2) {
      Q[j-1,i]<-0
    }
  }
}
R<-matrix(0,ns-2,ns-2)
for (i in 2:ns-1){
  for (j in 2:ns-1) {
    if (i==j) {
      R[j-1,i-1]<-1/3*(h[i-1]+h[i])
    }
    if (i==j-1) {
      R[j-1,i-1]<-1/6*h[i]
    }
    if (i==j+1){
      R[j-1,i-1]<-1/6*h[i]
    }
    if (abs(i-j)>=2) {
      R[j-1,i-1]<-0
    }
  }
}
K<-matrix(0,ns,ns)
K<-(Q%*%solve(R)%*%t(Q))
H<-0
  H<-solve(v+0.01*K)%*%v
  return(H)
}
#-------------------------------------------------------------------------------
#Hat matix for RS
hatps<-function(x,y){
  n<-length(y)
  v<-matrix(0,n,n)
  v<-vmat(x,0.7)
X<-cbind(matrix(1,n,1),x,x^2,x^3)
non<-n/2;
Ki<-seq(min(x),max(x),length.out = non);
A<-matrix(0,n,non)
for (i1 in 1:non){
  for (i2 in 1:n){
    A[i2,i1]<-(x[i2]-Ki[i1])^3*(x[i2]-Ki[i1]>0)
  }
}
ZZ<-cbind(X,A);
Z1<-matrix(0,4,4)
Z2<-matrix(0,4,non)
Z3<-matrix(0,non,4)
Z4<-diag(non)
D<-rbind(cbind(Z1,Z2),cbind(Z3,Z4))
#Selecting Smoothing Parameter with GCV
Hps<-0
  Hps<-ZZ%*%solve(t(ZZ)%*%v%*%ZZ+0.01*D)%*%t(ZZ)%*%v
  return(Hps)
}
#Hat matix for KS-------------------------------------------------------------------------
hatks<-function(x,y){
  kerf = function(aa) {
    res <- ((15/16)*(1-(aa^2)))*(abs(aa)<=1)
    return(res)
  }
  bw<-0.01
  n<-length(y)
  at<-seq(min(x),max(x),length.out=n)
  W<-matrix(0,n,n)
  sx<-sort(x)
  for (j1 in 1:n){
    u<-((at-x[j1]))/bw
    KK<-kerf(u)
    W[,j1]<-KK/sum(KK)
  }
  return(W)
}
#--------------------FUNCTIONS FOR CALCULATING CRITERIA SCORES--------------------------
#SMSE function
smsef<-function(y,yhat,H){
  n<-length(y)
  varmodel<-var(y-yhat)
  value_smse<-1/n*norm((diag(n)-H)%*%y,type="2")+varmodel*tr(H%*%t(H))
  return(value_smse)
}
#MAPE function
mapef<-function(y,yhat){
  n<-length(y)
  mape_v<-0
  mape_value=(1/n)*sum(abs(y-yhat)/y)
  return(mape_value)
}
#KL-N function
klnf<-function(y,yhat){
  ssquareterm<-0
  klnterm<-0
  ssquare<-0
  n<-length(y)
  for (s2 in 1:n){
    if (s2==1){
      ssquare[s2]<-(y[s2]-mean(y))^2
    }
    else{
      for (s3 in 1:s2-1){
        ssquareterm[s3]<-((y[s3]-mean(y[1:s2-1]))^2)
      }
      ssquare[s2]<-(1/(s2-1))*sum(ssquareterm)
      if(ssquare[s2]==0){
        ssquare[s2]<-1
      }
      klnterm[s2]<-(((y[s2]-yhat[s2])^2)/ssquare[s2])
    }
  }
  kln_value<-sqrt((1/n)*sum(klnterm))
  return(kln_value)
}
#IQR function
iqrf<-function(y,yhat){
  n<-length(y)
  iqr<-IQR(y)
  iqr_value<-sqrt((1/n)*sum(abs(y-yhat)/iqr^2))
  return(iqr_value)
}
#RSE function
rsef<-function(y,yhat){
  rseterm<-0
  n<-length(y)
  for (i in 2:n){
    rseterm[i]<-((y[i]-yhat[i])^2)/((y[i]-y[i-1])^2)
  }
  rse_value<-sqrt((1/n)*sum(rseterm))
  return(rse_value)
}
#RSE function
raef<-function(y,yhat){
  raeterm<-0
  n<-length(y)
  for (i in 2:n){
    raeterm[i]<-(abs(y[i]-yhat[i]))/(abs(y[i]-y[i-1]))
  }
  rae_value<-sqrt(mean(raeterm))
  return(rae_value)
}
#MSE function
msef<-function(y,yhat){
  n<-length(y)
  mse_value<-mean((y-yhat)^2)
  return(mse_value)
}
#------------------------------------------------------------------------------------------
#Function for generating explanatory variable "x"------------------------------------------
prodx<-function(n,spa){
  x<-0
  for (i in 1:n){
    x[i]<-spa*(i-0.5)/n
  }
  return(x)
}
#------------------------------------------------------------------------------------------
#Function for determining the detection limit
cutoffp<-function(y,cl,n){
  sy<-sort(y)
  noc<-cl*n
  cstart<-n-noc
  cutoff<-sy[cstart]
  return(cutoff)
}
#------------------------------------------------------------------------------------------
#Function for censor indicator-------------------------------------------------------------
censI<-function(y,cl,n){
  cens<-0
  sy<-sort(y)
  noc<-cl*n
  cstart<-n-noc
  for (j in 1:n) {
    if (y[j]<sy[cstart]) {
      cens[j]<-1
    }
    else {
      cens[j]<-0
    }
  }
  return(cens)
}
#------------------------------------------------------------------------------------------
#Funtion for censored time-series----------------------------------------------------------
cseries<-function(y,cens,n,cl){
  c<-0
  sy<-sort(y)
  noc<-cl*n
  cstart<-n-noc
  for (l in 1:n) {
    if (cens[l]==1){
      c[l]<-y[l]
    }
    else {
      c[l]<-sy[cstart]
    }
  }
  return(c)
}
#-------------------------------------------------------------------------------------------
#Function of augmentation and imputation and Obtaining augmented response variabel Yg-------
augmented<-function(y,cl,c,n,constant){
  Teta<-matrix(0,3,100)
  if (n<100){
  constant=2.1
  }
  if (n>=100){
    constant=25
  }
  Yg<-0
  sy<-sort(y)
  noc<-cl*n
  cstart<-n-noc
  T<-c
  sT<-sort(T)
  cut=max(T)
  cutoff<-cutoffp(y,cl,n)
  meanc0<-cutoff
  varc0<-var(T)
  obs<-sT[1:cstart]
  term<-mean(obs-mean(obs))
  v0<-meanc0+var(T)*(1/var(obs))*(term)
  deltaa0<-abs(varc0+var(T)-var(obs))
  delta0<-constant*sqrt(deltaa0)
  T1<-rtnorm(n,mean=v0,sd=delta0,lower=cut,upper=Inf)
  
  za<-acf(T,lag.max = 1,type = "covariance",plot=FALSE)
  autocov0<-za$acf[1]
  Teta[,1]<-c(v0,delta0,autocov0)
  tol<-5
  
  ll=2
  while (tol>=0.5){
    for (hh in 1:n) {
      if (T[hh]==cut) {
        Yg[hh]<-T1[hh]
      }
      else {
        Yg[hh]<-T[hh]
      }
    }
    
    sYg<-sort(Yg)
    zz<-acf(Yg,lag.max = 1,type = "covariance",plot=FALSE)
    obs<-sYg[1:cstart]
    cen<-sYg[cstart:n]
    meanc0<-mean(cen)
    varc0<-var(cen)
    term<-mean(obs-mean(obs))
    vi<-meanc0+var(T)*(1/var(obs))*(term)
    deltaa<-abs(varc0+var(T)-var(obs))
    delta<-sqrt(deltaa)*constant
    autocov<-zz$acf[1]
    #autocov<-npcov(Yg)
    Teta[,ll]<-c(vi,delta,autocov)
    T1<-rtnorm(n,mean=vi,sd=delta,lower=cut,upper=Inf)
    tol<-(t(Teta[,ll]-Teta[,ll-1])%*%(Teta[,ll]-Teta[,ll-1]))/(t(Teta[,ll-1])%*%(Teta[,ll-1]))
    ll=ll+1
  }
  return(Yg)
}
#---------------------------------------------------------------------------------------------
#Function for drawing plots------------------------------------------------------------------
ggtogether<-function(x,observed_data,RS,KS,SS,censored_data,n){
  library(ggplot2)
  g1<-matrix(c(x,observed_data),n,2)
  g2<-matrix(c(x,RS),n,2)
  g3<-matrix(c(x,censored_data),n,2)
  g4<-matrix(c(x,KS),n,2)
  g5<-matrix(c(x,SS),n,2)
  df1<-data.frame(g1)
  df2<-data.frame(g2)
  df3<-data.frame(g3)
  df4<-data.frame(g4)
  df5<-data.frame(g5)
  ggplot()+geom_point(data=df3,aes(x=x,y=censored_data,color="censored_data"))+geom_point(data=df1,aes(x=x,y=observed_data,color="observed_data"))+geom_line(data=df2,aes(x=x,y=RS,color="RS"),size=1)+geom_line(data=df4,aes(x=x,y=KS,color="KS"),size=1)+geom_line(data=df5,aes(x=x,y=SS,color="SS"),size=1)+scale_color_manual(values = c('observed_data'='black', 'censored_data'='red','RS'='blue','KS'='purple','SS'='green'))+theme_light()+theme(legend.title=element_blank())
  return(ggplot()+geom_point(data=df3,aes(x=x,y=censored_data,color="censored_data"))+geom_point(data=df1,aes(x=x,y=observed_data,color="observed_data"))+geom_line(data=df2,aes(x=x,y=RS,color="RS"),size=1)+geom_line(data=df4,aes(x=x,y=KS,color="KS"),size=1)+geom_line(data=df5,aes(x=x,y=SS,color="SS"),size=1)+scale_color_manual(values = c('observed_data'='black', 'censored_data'='red','RS'='blue','KS'='purple','SS'='green'))+theme_light()+theme(legend.title=element_blank()))
}
#-----------------------------------------------------------------------------------------------
#Function for Penalized Spline------------------------------------------------------------------
takeps<-function(x,y) {
  f<-smooth.Pspline(x,y,norder=3,spar=0.01)
  fhat<-f$ysmth
  return(fhat)
}
#-----------------------------------------------------------------------------------------------
#Function for Kernel Smoothing------------------------------------------------------------------
takeks<-function(x,y){
  f<-ksmooth(x,y,kernel =("normal"))
  ksfhat<-f$y
  ksfhat<-ksfhat[!is.na(ksfhat)]
  return(ksfhat)
}
#KERNEL SMOOTHING METHOD
takeks2<-function(x,y){
  kerf = function(aa) {
    res <- ((15/16)*(1-(aa^2)))*(abs(aa)<=1)
    return(res)
  }
  bw<-0.07
  n<-length(y)
  at<-seq(min(x),max(x),length.out=n)
  W<-matrix(0,n,n)
  sx<-sort(x)
  for (j1 in 1:n){
    u<-((at-x[j1]))/bw
    KK<-kerf(u)
    W[,j1]<-KK/sum(KK)
  }
  ksfhat<-W%*%y
  return(ksfhat)
}
#-----------------------------------------------------------------------------------------------
#Function for Smoothing spline------------------------------------------------------------------
takess<-function(x,y){
  f<-smooth.spline(x,y)
  ssfhat<-f$y
}
#-----------------------------------------------------------------------------------------------
#Shiny Application begins-----------------------------------------------------------------------
library(shiny)

ui <- fluidPage(
  titlePanel(title=h4("Censored Time-Series: Interactive Simulation Study", align="center")     
  ),
  
  sidebarLayout(
    sidebarPanel(
      sliderInput(inputId = "sim",label="Number of Simulation",value=200,min=30,max=500),
      sliderInput(inputId = "n",label="Sample size",value=121,min=35,max=300),
      sliderInput(inputId = "teta",label="Censoring Level",value=0.15,min=0.01,max=0.99),
      sliderInput(inputId = "ro",label="AR(1) coefficient (ro)",value=0.01,min=0,max=0.99),
      sliderInput(inputId = "spa",label="Spatial variation",value=6.4,min=1,max=25.6)
      #actionButton(inputId = "Clicks",label = "Run"),
    ),
    mainPanel(
      plotOutput("PC"),
      verbatimTextOutput("Measures1"),
      verbatimTextOutput("Measures2"),
      verbatimTextOutput("Measures3"),
      verbatimTextOutput("Measures4"),
      verbatimTextOutput("Measures5"),
      verbatimTextOutput("Measures6"),
      verbatimTextOutput("Measures7")
    )
  )
)

# Define server logic required to draw a histogram
server <- function(input, output) {
  x<-reactive({prodx(input$n,input$spa)})
  cl<-reactive(input$teta)
  ro<-reactive(input$ro)
  ei<-reactive({arima.sim(model=list(ar = ro()), n = input$n)*0.1+rnorm(input$n,mean=0,sd=0.1)})
  y<-reactive({log(sin(x())^2+52+ei())})
  cutoff<-reactive({cutoffp(y(),cl(),input$n)})
  cens<-reactive({censI(y(),cl(),input$n)})
  C<-reactive({cseries(y(),cens(),input$n,cl())})
  Yg<-reactive({augmented(y(),cl(),C(),input$n)})
  psfhat<-reactive({
    b<-matrix(0,input$n,input$sim)
    for (i in 1:input$sim){
      x1<-prodx(input$n,input$spa)
      ei1<-arima.sim(model=list(ar = ro()), n = input$n)*0.1+rnorm(input$n,mean=0,sd=0.1)
      y1<-log(sin(x1)^2+52+ei1)
      C1<-cseries(y1,cens(),input$n,cl())
      yg<-augmented(y1,cl(),C1,input$n)
      b[,i]<-takeps(x1,yg)
    }
    rowMeans(b)
  })
  ksfhat<-reactive({
    ksf<-matrix(0,input$n,input$sim)
    for (i in 1:input$sim){
      x1<-prodx(input$n,input$spa)
      ei1<-arima.sim(model=list(ar = ro()), n = input$n)*0.1+rnorm(input$n,mean=0,sd=0.1)
      y1<-log(sin(x1)^2+52+ei1)
      C1<-cseries(y1,cens(),input$n,cl())
      yg<-augmented(y1,cl(),C1,input$n)
      if (input$n>=100){
        ksf[,i]<-takeks(x1,yg)
      }
      else{
        ksf[,i]<-takeks2(x1,yg)
      }
    }
    rowMeans(ksf)
  })
  ssfhat<-reactive({
    ssf<-matrix(0,input$n,input$sim)
    for (i in 1:input$sim){
      x1<-prodx(input$n,input$spa)
      ei1<-arima.sim(model=list(ar = ro()), n = input$n)*0.1+rnorm(input$n,mean=0,sd=0.1)
      y1<-log(sin(x1)^2+52+ei1)
      C1<-cseries(y1,cens(),input$n,cl())
      yg<-augmented(y1,cl(),C1,input$n)
      ssf[,i]<-takess(x1,yg)
    }
    rowMeans(ssf)
  })
  #MSE values
  msess<-reactive({msef(Yg(),ssfhat())})
  mseks<-reactive({msef(Yg(),ksfhat())})
  msers<-reactive({msef(Yg(),psfhat())})
  #SMSE values
  smsess<-reactive({
    hss<-matrix(0,input$n,input$n)
    hss<-hatss(x(),Yg())
    smsef(Yg(),ssfhat(),hss)
    })
  smseks<-reactive({
    hks<-matrix(0,input$n,input$n)
    hks<-hatks(x(),Yg())
    smsef(Yg(),ksfhat(),hks)
    })
  smsers<-reactive({
    hps<-matrix(0,input$n,input$n)
    hps<-hatks(x(),Yg())
    smsef(Yg(),psfhat(),hps)
    })
  #MAPE values
  mapess<-reactive({mapef(Yg(),ssfhat())})
  mapeks<-reactive({mapef(Yg(),ksfhat())})
  mapeps<-reactive({mapef(Yg(),psfhat())})
  #KLN values
  klnss<-reactive({klnf(Yg(),ssfhat())})
  klnks<-reactive({klnf(Yg(),ksfhat())})
  klnps<-reactive({klnf(Yg(),psfhat())})
  #IQR values
  iqrss<-reactive({iqrf(Yg(),ssfhat())})
  iqrks<-reactive({iqrf(Yg(),ksfhat())})
  iqrps<-reactive({iqrf(Yg(),psfhat())})
  #RSE values
  rsess<-reactive({rsef(Yg(),ssfhat())})
  rseks<-reactive({rsef(Yg(),ksfhat())})
  rseps<-reactive({rsef(Yg(),psfhat())})
  #RAE values
  raess<-reactive({raef(Yg(),ssfhat())})
  raeks<-reactive({raef(Yg(),ksfhat())})
  raeps<-reactive({raef(Yg(),psfhat())})
  
  output$PC<-renderPlot({
    plot(C(), ylim = range(min(y()), max(y())),main="Fitted curves, Observed data vs. Censored data",xlab="index",ylab="Values of y",col="red",type="p",pch=19)
    par(new=TRUE)
    plot(y(), ylim = range(min(y()), max(y())),main="Fitted curves, Observed data vs. Censored data",xlab="index",ylab="Values of y",col="black",type="p",pch=19)
    par(new=TRUE)
    plot(psfhat(),ylim = range(min(y()), max(y())),xlab="index",ylab="Values of y",col="pink",type="l",lwd=2)
    par(new=TRUE)
    lines(ksfhat(),ylim = range(min(y()), max(y())),xlab="index",ylab="Values of y",col="blue",lwd=2)
    par(new=TRUE)
    lines(ssfhat(),ylim = range(min(y()), max(y())),xlab="index",ylab="Values of y",col="green",lwd=2)
    grid (NULL,NULL, lty = 6)
    legend(-2.8,min(y())+0.0096,legend=c("Censored data(c)","Observed Data(y)","RS","KS","SS"),pch=c(19,19,NaN,NaN,NaN),lty=c(0,0,1,1,1),col=c("red","black","pink","blue","green"))
    })
  output$Measures1<-renderPrint({
    print("MSE Values for Methods")
    print(" SS            KS           RS ");
    c(msess(),mseks(),msers())
    })
  output$Measures2<-renderPrint({
    print("SMSE Values for Methods")
    print(" SS            KS           RS ");
    c(smsess(),smseks(),smsers())
  })
  output$Measures3<-renderPrint({
    print("MAPE Values for Methods")
    print(" SS            KS           RS ");
    c(mapess(),mapeks(),mapeps())
  })
  output$Measures4<-renderPrint({
    print("KL-N Values for Methods")
    print(" SS      KS       RS ");
    c(klnss(),klnks(),klnps())
  })
  output$Measures5<-renderPrint({
    print("IQR Values for Methods")
    print(" SS       KS        RS ");
    c(iqrss(),iqrks(),iqrps())
  })
  output$Measures6<-renderPrint({
    print("RSE Values for Methods")
    print(" SS         KS        RS ");
    c(rsess(),rseks(),rseps())
  })
  output$Measures7<-renderPrint({
    print("RAE Values for Methods")
    print(" SS       KS       RS ");
    c(raess(),raeks(),raeps())
  })
  #observe({print((input$Clicks))})
}

# Run the application 
shinyApp(ui = ui, server = server)
