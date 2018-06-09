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
library(ggplot2)
library(RCurl)
library(dplyr)
#function of determining the detection limit
prodx<-function(n,spa){
  x<-0
  for (i in 1:n){
    x[i]<-spa*(i-0.5)/n
  }
  return(x)
}
cutoffp<-function(y,cl,n){
  sy<-sort(y)
  noc<-cl*n
  cstart<-n-noc
  cutoff<-sy[cstart]
  return(cutoff)
}
#function for censor indicator 
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
#funtion for censored time-series
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
#function of augmentation and imputation
augmented<-function(y,cl,c,n){
  Teta<-matrix(0,3,100)
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
  delta0<-sqrt(deltaa0)*1.5
  T1<-rtnorm(n,mean=v0,sd=delta0,lower=cut,upper=Inf)
  
  za<-acf(T,lag.max = 1,type = "covariance",plot=FALSE)
  autocov0<-za$acf[1]
  Teta[,1]<-c(v0,delta0,autocov0)
  tol<-5
  
  ll=2
  while (tol>=0.005){
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
    delta<-sqrt(deltaa)*1.5
    autocov<-zz$acf[1]
    #autocov<-npcov(Yg)
    Teta[,ll]<-c(vi,delta,autocov)
    T1<-rtnorm(n,mean=vi,sd=delta,lower=cut,upper=Inf)
    tol<-(t(Teta[,ll]-Teta[,ll-1])%*%(Teta[,ll]-Teta[,ll-1]))/(t(Teta[,ll-1])%*%(Teta[,ll-1]))
    ll=ll+1
  }
  return(Yg)
}
ggtogether<-function(x,y1,y2,c,n){
  library(ggplot2)
  g1<-matrix(c(x,y1),n,2)
  g2<-matrix(c(x,y2),n,2)
  g3<-matrix(c(x,c),n,2)
  df1<-data.frame(g1)
  df2<-data.frame(g2)
  df3<-data.frame(g3)
  ggplot()+geom_point(data=df3,aes(x=x,y=c,color="c"))+geom_point(data=df1,aes(x=x,y=y1,color="y1"))+geom_line(data=df2,aes(x=x,y=y2,color="y2"))+scale_color_manual(values = c('y1'='black', 'c'='red','y2'='blue'))+theme_light()
  return(ggplot()+geom_point(data=df3,aes(x=x,y=c,color="c"))+geom_point(data=df1,aes(x=x,y=y1,color="y1"))+geom_line(data=df2,aes(x=x,y=y2,color="y2"))+scale_color_manual(values = c('y1'='black', 'c'='red','y2'='blue'))+theme_light())
}

takeps<-function(x,y,lambda) {
  f<-smooth.Pspline(x,y,norder=3,spar=lambda)
  fhat<-f$ysmth
  return(fhat)
}


#-------------------------------------------------------------
library(shiny)

ui <- fluidPage(
  titlePanel(title=h4("Censored time-series interactive simulation", align="center")     
  ),
  sliderInput(inputId = "n",label="Sample size",value=30,min=20,max=300),
  sliderInput(inputId = "teta",label="Censoring Level",value=0.25,min=0.01,max=0.99),
  sliderInput(inputId = "ro",label="AR(1) coefficient (ro)",value=0.01,min=0,max=0.99),
  sliderInput(inputId = "spa",label="Spatial variation",value=6.4,min=1,max=25.6),
  sliderInput(inputId = "lambda",label="Smoothing parameter",value=0.05,min=0.000001,max=0.5),
  #actionButton(inputId = "Clicks",label = "Run"),
  plotOutput("PC"),
  verbatimTextOutput("Measures")
)

# Define server logic required to draw a histogram
server <- function(input, output) {
  
  x<-reactive({prodx(input$n,input$spa)})
  cl<-reactive(input$teta)
  ro<-reactive(input$ro)
  ei<-reactive({arima.sim(model=list(ar = ro()), n = input$n)*0.25})
  y<-reactive({log(sin(x())^2+52+ei())})
  cutoff<-reactive({cutoffp(y(),cl(),input$n)})
  cens<-reactive({censI(y(),cl(),input$n)})
  C<-reactive({cseries(y(),cens(),input$n,cl())})
  Yg<-reactive({augmented(y(),cl(),C(),input$n)})
  psfhat<-reactive({takeps(x(),Yg(),input$lambda)})
  MSE<-reactive({mean((y()-psfhat())^2)})
  output$PC<-renderPlot({ggtogether(x(),y(),psfhat(),C(),input$n)})
  output$Measures<-renderPrint({MSE()})
  #observe({print((input$Clicks))})
}

# Run the application 
shinyApp(ui = ui, server = server)

