#ustalanie katalogu domowego gdzie beda znajdowac sie wszystkie pliki
setwd("C:/Users/XXX/")

#instalacja niezbednych pakietow
install.packages(c("fMultivar", "fAssets", "ecodist",
                   "energy","mvnormtest"))
install.packages(c("quantmod","PerformanceAnalytics","fPortfolio"))
install.packages("matlab")

source("RobustBayesianAllocation.R")

#dolaczanie niezbednych pakietow
library(quantmod)
library(fPortfolio)
library(PerformanceAnalytics)
library(matlab)

#dane do benchmarku indeks wig, rentownosc 10-letnich obligacji wibor3m
benchmark<-c("wig","10ply.b","plopln3m")


#pobieranie notowan
x<-read.csv2("Quant_Invest_Fundusze.csv",header=T,stringsAsFactors = F)


#pobieranie danych do benchmarku
y<-list()
for(i in 1:length(benchmark)){
  y[[i]]<-read.csv(paste("http://stooq.pl/q/d/l/?s=",benchmark[i],"&i=d",sep=""),header=T,stringsAsFactors = F)
  y[[i]]<-xts(y[[i]]$Zamkniecie,order.by=as.Date(y[[i]]$Data))
}
#notowania
notowania<-xts(x[,-1],order.by=as.Date(x[,1]))
notowania<-na.locf(notowania)
storage.mode(notowania)<-"numeric"
#benchmarki
wzorcowe<-Reduce(merge,y)
names(wzorcowe)<-benchmark
wzorcowe<-na.locf(wzorcowe)


#dane do konstrukcji wag portfela obejmuja okres od 2000 do 2017 roku
stopyzwrotu<-na.omit(100*diff(log(notowania)))["2000/2017"]


#Elementy konstrukcji portfela efektywnego - wyznaczanie mozliwosci inwestycyjnych
scenarios <- dim(stopyzwrotu)[1] #liczba obserwacji
assets <- dim(stopyzwrotu)[2] #liczba aktywow w portfelu
data_ts <- as.timeSeries(stopyzwrotu) #przeksztalcenie na szereg typu ts
spec <- portfolioSpec() #wywo≥anie standardowej specyfikacji portfela
setSolver(spec) <- "solveRquadprog" #wybor metody optymalizacji
setNFrontierPoints(spec) <- 20  #liczba punktow na granicy efektywnoúci
#Wykluczamy krotka sprzedaz
constraints <- c("LongOnly")
portfolioConstraints(data_ts, spec, constraints)
frontier <- portfolioFrontier(data_ts, spec, constraints)
print(frontier)
frontierPlot(object=frontier)
tailoredFrontierPlot(object = frontier)
weightsPlot(frontier, col = rainbow(assets))



#niezbedne funkcje


maxriskPortfolio <-
  function (data, spec = portfolioSpec(), constraints = "LongOnly")
  {
    Data = portfolioData(data, spec)
    data <- getSeries(Data)
    targetRiskFun <- function(x, data, spec, constraints) {
      setTargetReturn(spec) = x[1]
      Solver = match.fun(getSolver(spec))
      ans = Solver(data, spec, constraints)
      targetRisk = -ans$objective
      attr(targetRisk, "weights") <- ans$weights
      attr(targetRisk, "status") <- ans$status
      return(targetRisk)
    }
    portfolio <- optimize(targetRiskFun, interval = range(getMu(Data)),
                          data = Data, spec = spec, constraints = constraints,
                          tol = .Machine$double.eps^0.5)
    
    setWeights(spec) <- attr(portfolio$objective, "weights")
    setStatus(spec) <- attr(portfolio$objective, "status")
    portfolio = feasiblePortfolio(data, spec, constraints)
    portfolio@call = match.call()
    portfolio@title = "Maximum Risk Portfolio"
    portfolio
  } 

#odporna optymalizacja bayesowska - parametry wejsciowe
J = 50 # number of simulations
T = dim(stopyzwrotu)[1] #liczba obserwacji
N = dim(stopyzwrotu)[2] # number of assets in the market
r = mean(cor(stopyzwrotu)) # overall correlation in constant correlation matrix
min_s = min(colSds(stopyzwrotu)) # min volatility among the N assets
max_s = max(colSds(stopyzwrotu)) # max volatility among the N assets
NumPortf = 10 # number of discretizations for efficient frontier
p_m = 0.02 # aversion to estimation risk for mu (zgodnie ze wsk. SRRI)
p_s = 0.099 # aversion to estimation risk for sigma (zgodnie ze wsk. SRRI)

####################################################################
# true market parameters
####################################################################
C = ( 1 - r ) * eye( N ) + r * ones( N , N ) # creates a homogenous correlation matrix
step_s = ( max_s - min_s ) / ( N - 1 ) # 1st asset will have min volatility...
s = seq( min_s , max_s , step_s ) # ... last asset will have maximum volatility
S = diag(s) %*% C %*% diag(s) # fake covariance matrix with equally spaced volatilities

# Note the means are defined in such a way that a mean-variance optimization would yield an equally weighted portfolio
# fake mean matrix : mus = 2.5 * Sigma / N
M = 2.5 * S %*% ones( N , 1 ) / N

efficientFrontier<-function (discretizations, cov, mu, longonly = FALSE) 
{
  N = nrow(cov)
  firstDegree = zeros(N, 1)
  secondDegree = cov
  Aeq = ones(1, N)
  beq = 1
  A = eye(N)
  b = zeros(N, 1)
  if (!longonly) {
    Aqp = t(Aeq)
    bqp = beq
  }
  else {
    Aqp = t(rbind(Aeq, A))
    bqp = c(beq, b)
  }
  minVolWeights = solve.QP(secondDegree, firstDegree, Aqp, 
                           bqp, length(beq))$solution
  minVolRet = minVolWeights %*% mu
  maxRet = max(mu)
  step = (maxRet - minVolRet)/(discretizations - 1)
  targetReturns = seq(minVolRet, maxRet, step)
  weights = minVolWeights
  volatility = sqrt(minVolWeights %*% cov %*% minVolWeights)
  returns = minVolRet
  for (i in 2:(discretizations - 1)) {
    Aeq = ones(1, N)
    Aeq = rbind(Aeq, t(mu))
    beq = c(1, targetReturns[i])
    if (!longonly) {
      Aqp = t(Aeq)
      bqp = beq
    }
    else {
      Aqp = t(rbind(Aeq, A))
      bqp = c(beq, b)
    }
    solvedWeights = solve.QP(secondDegree, firstDegree, Aqp, 
                             bqp, 1)$solution
    weights = rbind(weights, solvedWeights)
    volatility = c(volatility, sqrt(solvedWeights %*% cov %*% 
                                      solvedWeights))
    returns = c(returns, solvedWeights %*% mu)
  }
  return(list(returns = returns, volatility = volatility, weights = weights))
}


####################################################################
# conduct Monte carlo simulation
####################################################################

# initialize variables
meanVarMus = meanVarVols = trueMus = trueVols = bayesianMus = bayesianVols = robustMus = robustVols = list()

# construct efficient sample, bayesian, and robust bayesian frontier for each simulation
for( j in 1:J )
{
  # Sample T draws from the true covariance matrix
  rets = mvrnorm( T , M , S ) 

  # construct mean-variance frontier using sample estimate.
  mean = colMeans( rets ) # get mean vector
  cov = cov( rets ) # cov vector  
  sampleFrontier = efficientFrontier( NumPortf , cov , mean , TRUE ) 
  # returns a list of returns, volatility, and assets weights along the frontier. Each row represents a point on the frontier
  # construct mean-variance efficient portfolio based on true Mu and sigma  
  trueFrontier = efficientFrontier( NumPortf , S , M , TRUE ) 
  # Bayesian prior for covariance and mu's (an arbitrary prior model of covariance and returns)
  # the covariance prior is equal to the sample covariance on the principal diagonal
  cov_prior  = diag( diag( cov ) ) 
  
  # set the prior expected returns for each asset to : mus = .5 * Sigma(1/N). Incidentally, this ensures there is a perfect positive linear relationship between asset variance and asset expected  return
  mean_prior = .99 * cov_prior %*% rep( 1/N , N ) 
  
  # set the confidence in the prior as twice the confidence in the sample and blend the prior with the sample data
  posterior = PartialConfidencePosterior( mean_sample = mean , cov_sample = cov , mean_prior = mean_prior , cov_prior = cov_prior , 
                                          relativeConfidenceInMeanPrior = 2 , relativeConfidenceInCovPrior = 2 , sampleSize = nrow( rets ) )
  cov_post = posterior$cov_post ; mean_post = posterior$mean_post ; time_post = posterior$time_post ; nu_post = posterior$nu_post ; rm( posterior )
  
  # construct Bayesian frontier using blended mu and Sigma, and identify robust portfolio
  # returns a set of Bayesian efficient portfolios: a list of returns, volatility, and assets weights along the posterior frontier. Each row represents a point on the frontier
  # and the returns, volatility, and assets of the most robust portfolio in the set
  
  pickVol = round( .99 * NumPortf ) # Picks the 90% highest volatility ( a parameter )...
  volatility = ( sampleFrontier[[ "volatility" ]][ pickVol ] ) ^ 2 # ...on the sample *efficient* frontier. On the efficient *sample* frontier. This is why the problem is a second-order cone programming problem. TODO: why use sample frontier?
  
  if ( is.na(volatility) == TRUE ) { stop( "The chosen volatility is too high" ) }
}


  frontierResults = robustBayesianPortfolioOptimization( mean_post = mean_post , 
                                                         cov = cov_post , 
                                                         nu_post = nu_post ,
                                                         time_post = time_post,
                                                         riskAversionMu = p_m , 
                                                         riskAversionSigma = p_s , 
                                                         discretizations = NumPortf ,
                                                         longonly = TRUE ,
                                                         volatility = volatility )


   
  bayesianFrontier = frontierResults$bayesianFrontier ; robustPortfolio = frontierResults$robustPortfolio ; rm(frontierResults) 
  
  for( j in 1:J )
  {# initialize parameters
  mumv = volmv = mutrue = voltrue = mubay = volbay = NULL
  
  # for each  portfolios along the sample and Bayesian frontiers, measure the actual returns and actual volatility based on the true returns/true covariance
  for( k in 1:( NumPortf - 1 ) ) 
  {      
    # Notice when plotting the sample-based allocation is broadly scattered in inefficient regions
    weightsMV = sampleFrontier[[ "weights" ]][ k , ] # retrieve the weights assigned to the k'th portfolio along the sample frontier
    mumv = c( mumv , weightsMV %*% M ) # given the optimal weights from sample estimates of mu and Sigma, measure the actual return using the true asset means
    volmv = c( volmv , ( weightsMV %*% S %*% weightsMV ) ) # given the optimal weights from the sample estimates of mu and Sigma, measure the actual variance of the portfolio
    
    # measure actual performance using true mu and cov
    weightsMVTrue = trueFrontier[[ "weights" ]][ k , ] # retrieve the weights assigned to the k'th portfolio along the true frontier
    mutrue = c( mutrue , weightsMVTrue %*% M ) # given the optimal weights from actual values of mu and Sigma, measure the actual return using the true asset means
    voltrue = c( voltrue , ( weightsMVTrue %*% S %*% weightsMVTrue ) ) # given the optimal weights from the sample estimates of mu and Sigma, measure the actual variance of the portfolio    
    
    weightsBay = bayesianFrontier[[ "weights" ]][ k , ]
    mubay = c( mubay , weightsBay %*% M ) # given the optimal weights from Bayesian estimates of mu and Sigma, measure the actual return using the true asset means
    volbay = c( volbay , ( weightsBay %*% S %*% weightsBay ) ) # given the optimal weights from the Bayesian estimates of mu and Sigma, measure the actual variance of the portfolio
  }   
  
  # measure the actual performance of the most Robust portfolio along the Bayesian efficient frontier
  weightsRob = robustPortfolio$weights
  murob = weightsRob %*% M
  volrob = weightsRob %*% S %*% weightsRob
  
  # collect actual return and actual variances results for each portfolio in each simulation
  meanVarMus[[ j ]] = mumv # list of actual returns along efficient frontier for each simulation based on portfolio constructed using sample mean and sample co-variance
  meanVarVols[[ j ]] = volmv # ...and the list of actual variances along efficient frontier
  bayesianMus[[ j ]] = mubay # list of actual returns based on bayesian mixing of prior and data sampled from true distribution
  bayesianVols[[ j ]] = volbay # ...and the list of associated actual variances
  robustMus[[ j ]] = murob # list of actual return based on robust allocation... Note only one robust portfolio per simulation j is identified.
  robustVols[[ j ]] = volrob # ...and the list of associated actual variances. Note only one robust portfolio per simulation j is identified.
  trueMus[[ j ]] = mutrue # list of actual return based on optimizing with the true mus...
  trueVols[[ j ]] = voltrue # ...and the list of associated actual variances  
}

# Plot sample, bayesian, and robust mean/variance portfolios
library( ggplot2 )

# create dataframe consisting of actual returns, actual variance, and sample indicator    
actualReturns = unlist( meanVarMus ) ; actualVariance = unlist( meanVarVols )
plotData1 = data.frame( actualReturns = actualReturns, actualVariance = actualVariance , type = "Sample" )
actualReturns = unlist( bayesianMus ) ; actualVariance = unlist( bayesianVols )
plotData2 = data.frame( actualReturns = actualReturns, actualVariance = actualVariance , type = "Bayesian" )
actualReturns = unlist( robustMus ) ; actualVariance = unlist( robustVols )
plotData3 = data.frame( actualReturns = actualReturns, actualVariance = actualVariance , type = "Robust Bayesian" )
actualReturns = unlist( trueMus ) ; actualVariance = unlist( trueVols )
plotData4 = data.frame( actualReturns = actualReturns, actualVariance = actualVariance , type = "True frontier" )
plotData = rbind( plotData1 , plotData2 , plotData3 , plotData4 ) ; rm( plotData1 , plotData2 , plotData3 , actualReturns , actualVariance )

# build plot with overlays    
# Notice when plotting the the Bayesian portfolios are shrunk toward the prior. Therefore they 
# are less scattered and more efficient, although the prior differs significantly from the true market parameters.
ggplot( data = plotData ) + geom_point( aes_string( x = "actualVariance" , y = "actualReturns" , color = "type"  ) )


#portfele w zaleznosci od profilu inwestora
maxsharpe<-tangencyPortfolio(data_ts) #maksymalizujacy wsk. Sharpe
maxret<-maxriskPortfolio(data_ts) #maksymalizujacy stope zwrotu
minrisk<-minriskPortfolio(data_ts) #minimalizujacy ryzyko

wagi1<-maxsharpe@portfolio@portfolio$weights
wagi2<-maxret@portfolio@portfolio$weights
wagi3<-minrisk@portfolio@portfolio$weights
wagi4<-robustPortfolio$weights
#udzialy
wagi1 #portfel Sharpe
wagi2 #portfel maks. zwrotu
wagi3 #portfel min. ryzyka
wagi4 #robust bayesian portfolio z uwzgl. awersji do ryzyka inwestora
#porównanie efektywności w stosunku do mWIG40 w horyzoncie inwestycyjnym tj. w roku 2018

Dane1<-t(wagi1%*%t(notowania["2018/2018"]))
Dane1<-xts(Dane1,order.by=as.Date(index(notowania["2018/2018"])))
Dane2<-t(wagi2%*%t(notowania["2018/2018"]))
Dane2<-xts(Dane2,order.by=as.Date(index(notowania["2018/2018"])))
Dane3<-t(wagi3%*%t(notowania["2018/2018"]))
Dane3<-xts(Dane3,order.by=as.Date(index(notowania["2018/2018"])))
Dane4<-t(wagi4%*%t(notowania["2018/2018"]))
Dane4<-xts(Dane4,order.by=as.Date(index(notowania["2018/2018"])))


#efektywnosc wzgledem indeksu WIG

indeks<-wzorcowe[,1]["2018/2018"]
reta <- merge(indeks,Dane1,Dane2, Dane3,Dane4)
reta<-ROC(reta)
reta<-na.omit(reta)
names(reta)<-c("indeks","Sharpe","minrisk","maxret","robustBayesian")


# Wyznaczanie efektywnosci portfeli inwestycyjnych w okresie inwestowania
chart.Boxplot(reta,main="Stopa zwrotu vs. ryzyko",xlab="")
par(mfrow=c(3,1))
chart.CumReturns(reta,main="Skumulowana stopa zwrotu",ylab="",lwd=2,
                 minor.ticks = FALSE,
                 legend.loc ="topleft",cex.legend=0.4, col=c("black","red","green","blue","grey"))
chart.BarVaR(reta,main="Dzienna stopa zwrotu")
chart.Drawdown(reta, ylab="",main="Spadek wartosci portfela")
eq1 <- exp(cumsum(reta))
summary(eq1)
table.Stats(reta)
table.Variability(reta)
table.SpecificRisk(reta[,-1],reta[,1])
table.InformationRatio(reta[,-1],reta[,1])
table.Distributions(reta)
table.CAPM(reta[,-1],reta[,1],Rf=0)
table.Drawdowns(reta,top=10)
table.DownsideRisk(reta)
table.DrawdownsRatio(reta)
table.DownsideRiskRatio(reta)
table.AnnualizedReturns(reta)


#efektywnosc wzgledem indeksu rentownosci obligacji

indeks<-wzorcowe[,2]["2018/2018"]
reta <- merge(indeks,Dane1,Dane2, Dane3,Dane4)
reta<-ROC(reta)
reta<-na.omit(reta)
names(reta)<-c("indeks","Sharpe","minrisk","maxret","robustBayesian")



# Wyznaczanie efektywnosci portfeli inwestycyjnych w okresie inwestowania
chart.Boxplot(reta,main="Stopa zwrotu vs. ryzyko",xlab="")
par(mfrow=c(3,1))
chart.CumReturns(reta,main="Skumulowana stopa zwrotu",ylab="",lwd=2,
                 minor.ticks = FALSE,
                 legend.loc ="topleft",cex.legend=0.4, col=c("black","red","green","blue","grey"))
chart.BarVaR(reta,main="Dzienna stopa zwrotu")
chart.Drawdown(reta, ylab="",main="Spadek wartosci portfela")
eq1 <- exp(cumsum(reta))
summary(eq1)
table.Stats(reta)
table.Variability(reta)
table.SpecificRisk(reta[,-1],reta[,1])
table.InformationRatio(reta[,-1],reta[,1])
table.Distributions(reta)
table.CAPM(reta[,-1],reta[,1],Rf=0)
table.Drawdowns(reta,top=10)
table.DownsideRisk(reta)
table.DrawdownsRatio(reta)
table.DownsideRiskRatio(reta)
table.AnnualizedReturns(reta)


#efektywnosc wzgledem indeksu WIBOR3M - proxy dla oprocentowania lokat

indeks<-wzorcowe[,3]["2018/2018"]
reta <- merge(indeks,Dane1,Dane2, Dane3,Dane4)
reta<-ROC(reta)
reta<-na.omit(reta)
names(reta)<-c("indeks","Sharpe","minrisk","maxret","robustBayesian")


# Wyznaczanie efektywnosci portfeli inwestycyjnych w okresie inwestowania
chart.Boxplot(reta,main="Stopa zwrotu vs. ryzyko",xlab="")
par(mfrow=c(3,1))
chart.CumReturns(reta,main="Skumulowana stopa zwrotu",ylab="",lwd=2,
                 minor.ticks = FALSE,
                 legend.loc ="topleft",cex.legend=0.4, col=c("black","red","green","blue","grey"))
chart.BarVaR(reta,main="Dzienna stopa zwrotu")
chart.Drawdown(reta, ylab="",main="Spadek wartosci portfela")
eq1 <- exp(cumsum(reta))
summary(eq1)
table.Stats(reta)
table.Variability(reta)
table.SpecificRisk(reta[,-1],reta[,1])
table.InformationRatio(reta[,-1],reta[,1])
table.Distributions(reta)
table.CAPM(reta[,-1],reta[,1],Rf=0)
table.Drawdowns(reta,top=10)
table.DownsideRisk(reta)
table.DrawdownsRatio(reta)
table.DownsideRiskRatio(reta)
table.AnnualizedReturns(reta)



