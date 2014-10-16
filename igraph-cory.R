# Basic igraph functions

plot.onemode <- function(
    graph, vertex.shape = 'circle', vertex.color = 'SkyBlue2',
    vertex.label.color = 'white',
    vertex.size = 2 + 30 / (vcount(graph) ^ 2),
    edge.width = .5 + 2 / ecount(graph), edge.color = 'black', ...) {
    plot(graph, layout = layout.fruchterman.reingold(graph),
         vertex.shape = vertex.shape, vertex.color = vertex.color,
         vertex.label.color = vertex.label.color, vertex.size = vertex.size,
         edge.width = edge.width, edge.color = edge.color, ...)
}

plot.twomode <- function(
    bigraph, vertex.shape = c('circle', 'square'),
    vertex.color = c('SkyBlue2', 'lightcoral'),
    vertex.label.color = rep('black', 2),
    vertex.size = c(16 + 30 / (vcount(bigraph) ^ 2),
                    12 + 24 / (vcount(bigraph) ^ 2)),
    edge.width = .5 + 2 / ecount(bigraph), edge.color = 'black', ...) {
    
    plot(bigraph, layout = layout.fruchterman.reingold(bigraph),
         vertex.shape = vertex.shape[V(bigraph)$type + 1],
         vertex.color = vertex.color[V(bigraph)$type + 1],
         vertex.label.color = vertex.label.color[V(bigraph)$type + 1],
         vertex.size = vertex.size[V(bigraph)$type + 1],
         edge.width = edge.width, edge.color = edge.color, ...)
}


# GRAPH OBJECT MANIPULATION

# Extract the largest component of a graph as a new graph
largest.component <- function(graph) {
    if(is.connected(graph) == TRUE) return(graph)
    decompose.graph(
        graph,
        max.comps = 1,
        min.vertices = max(clusters(graph)$csize)
    )[[1]]
}


# STATISTICS AND DISTRIBUTIONS: EDGES AND CONNECTEDNESS

# joint degree distribution
joint.degree <- function(graph) {
    d <- degree(graph); dmax <- max(d)
    el <- get.edgelist(graph, names = FALSE)
    dl <- as.data.frame(cbind(d[el[, 1]], d[el[, 2]]))
    dd <- aggregate(dl, by = dl[, 1:2], length)
    jdmat <- matrix(0, nr = dmax, nc = dmax)
    for(i in 1:dim(dd)[1]) jdmat[dd[i, 1], dd[i, 2]] <- dd[i, 3]
    jdmat + t(jdmat)
}

# http://web.archiveorange.com/archive/v/yj6N4iYyQO7lBJzoYXsT


# STATISTICS AND DISTRIBUTIONS: ASSORTATIVE MIXING

# second-order assortativity (Zhou???Cox)
second.order.assortativity <- function(graph, coeff = 'max') {
    stop('Implementation incomplete')
}
# second.order.assortativity(graph)
# second.order.assortativity(graph, coeff = 'max')

# productivity-cooperativity correlation
modal.assortativity <- function(bigraph) {
    el <- get.edgelist(bigraph, names = FALSE)
    a <- degree(bigraph, v = el[, 1]) - 1
    q <- degree(bigraph, v = el[, 2]) - 1
    (mean(a * q) - mean(a) * mean(q)) / (sd(a) * sd(q))
}


# STATISTICS AND DISTRIBUTIONS: S-METRIC

# s-metric (Li et al)
s.metric <- function(graph) {
    ge <- get.edges(graph, E(graph))
    sum(degree(graph, ge[, 1]) * degree(graph, ge[, 2]))
}

# graphicality test (Tripathi???Vijay)
is.graphical <- function(degseq) {
    ds <- sort(degseq[which(degseq != 0)], decreasing = TRUE)
    if(length(ds) == 1) return(FALSE)
    S <- sum(ds)
    if(S %% 2 != 0) return(FALSE)
    if(S == 0) return(TRUE)
    p <- length(ds)
    m <- rev(hist(ds, breaks = 0:max(ds) + .5, plot = FALSE)$counts)
    m <- m[which(m != 0)]
    sigma <- sapply(1:length(m), function(k) sum(m[1:k]))
    LHS <- sapply(sigma, function(x) sum(ds[1:x]))
    RHS1 <- sigma * (sigma - 1)
    RHS2 <- c(sapply(sigma[1:(length(sigma) - 1)], function(x) sum(
        sapply(ds[(x + 1):p], function(y) min(x,y))
    )), 0)
    RHS <- RHS1 + RHS2
    sigma.TF <- ((LHS <= RHS) | (is.na(RHS)))
    return(all(sigma.TF))
}

# approximate s_max (Beichl???Cloteaux; implementation: Brunson)
smax.approx.graph <- function(degseq) {
    stopifnot(is.numeric(degseq))
    ds <- sort(degseq[which(degseq != 0)], decreasing = TRUE)
    p <- length(ds)
    if(p == 0) return(graph.empty(n = 0, directed = FALSE)) else d <- ds[1]
    m <- rev(hist(ds, breaks = 0:d + .5, plot = FALSE)$counts)
    sigma <- sapply(1:d, function(k) sum(m[1:k]))
    NZ <- if(d == tail(ds, n = 1)) rep(0, p) else
        sigma * (sigma - 1) + c(sapply(1:(d - tail(ds, n = 1)), function(i) {
            k <- 1 + if(sigma[i] < d) max(sigma[i], sigma[d - sigma[i]]) else sigma[i]
            sum((k - 1 - sigma[i]) * sigma[i], sum(ds[k:p]), na.rm = TRUE)
        }), rep(0, tail(ds, n = 1))) - sapply(sigma, function(x) sum(ds[1:x]))
    if(any(NZ < 0)) stop('NZ < 0')
    edges <- c()
    n1 <- 1
    n2 <- n1 + 1
    while(any(ds[n1:p] > 0)) {
        while(ds[n1] > 0) {
            if(n2 == p + 1) stop(
                paste('Cannot complete graph: ds = ', ds, '; n1 = ', n1, sep = '')
            )
            if(ds[n2] > 0) {
                m12 <- d - ds[c(n1, n2)] + 1
                sigma.alt <- sigma
                NZ.alt <- NZ
                for(k in m12) {
                    NZ.alt[k:d] <- NZ.alt[k:d] + c(d - k + 1, rep(1, d - k))
                    NZ.alt[k] <- NZ.alt[k] - 2 * (sigma.alt[k] - 1)
                    ell <- min(d - sigma.alt[k] + 1, d)
                    NZ.alt[k] <- NZ.alt[k] + min(sigma.alt[k] - 1, d - k) -
                        if(k < ell) (sigma.alt[ell] - sigma.alt[k]) else 0
                    if(k > 1) for(j in 1:(k - 1)) {
                        NZ.alt[j] <- NZ.alt[j] - if(k + sigma.alt[j] > d) 1 else 0
                    }
                    sigma.alt[k] <- sigma.alt[k] - 1
                }
                if(all(NZ.alt >= 0)) {
                    edges <- append(edges, c(n1, n2))
                    ds[c(n1, n2)] <- ds[c(n1, n2)] - 1
                    for(k in m12) if(k == d) m[k] <- m[k] - 1 else {
                        m[c(k, k + 1)] <- m[c(k, k + 1)] + c(-1, 1)
                    }
                    sigma <- sigma.alt
                    NZ <- NZ.alt
                }
            }
            n2 <- n2 + 1
        }
        n1 <- n1 + 1
        n2 <- n1 + 1
        while((m[1] == 0) & (length(m) > 1)) {
            m <- m[2:d]
            sigma <- sigma[2:d]
            NZ <- NZ[2:d]
            d <- d - 1
        }
    }
    return(graph(edges, directed = FALSE))
}

# perform s_max approximation across connected subgraphs
smax.componentwise <- function(graph) {
    comp.inds <- clusters(graph)
    smax.graph <- graph.empty(n = 0, directed = FALSE)
    for(i in 1:comp.inds$no) smax.graph <- graph.disjoint.union(smax.graph,
                                                                smax.approx.graph(degree(graph, which(comp.inds$membership == i))))
    return(smax.graph)
}

# S-metric (s(g) - s_min) / (s_max - s_min) (Li et al)
S.metric <- function(graph) {
    D <- sort(degree(graph))
    Z <- rep(D, D)
    smin <- sum(Z * rev(Z)) / 2
    (s.metric(graph) - smin) / (s.metric(smax.approx.graph(D)) - smin)
}


# STATISTICS AND DISTRIBUTIONS: CLUSTERING

# approximate clustering corrected for assortativity (Soffer and Vasquez 2005)
soffer.vasquez.transitivity <- function(
    graph, vids = V(graph), type = 'global', mode = 'approx'
) {
    stopifnot(mode == 'approx')
    k <- degree(graph)
    t <- transitivity(graph, vids = vids, type = 'local') * choose(k[vids], 2)
    Omega <- sapply(neighborhood(graph, 1, nodes = vids), function(vec) {
        k0 <- length(vec) - 1
        if(k0 < 1) NaN else
            floor(sum(sapply(vec[-1], function(v) min(k0, k[v])) - 1) / 2)
    })
    if(type == 'local') t / Omega else
        if(type == 'global') sum(t, na.rm = TRUE) / sum(Omega, na.rm = TRUE) else
            return(list(stratified = data.frame(Omega = Omega, t = t),
                        global = sum(t, na.rm = TRUE) / sum(Omega, na.rm = TRUE)))
}


# PREFERENTIAL ATTACHMENT

# Vectors of current pair counts by distance and of new edge counts by same
distance.weight.link <- function(g, Delta = 1) {
  # Before- and after-graphs
  y <- max(E(g)$year) - Delta + 1
  w <- which(E(g)$year >= y)
  f <- delete.edges(g, edges = w)
  E(f)$weight <- 1; f <- simplify(f, edge.attr.comb = list(weight = 'sum'))
  h <- delete.edges(g, edges = setdiff(E(g), w))
  E(h)$weight <- 1; h <- simplify(h, edge.attr.comb = list(weight = 'sum'))
  # Edgelist from after-graph
  el <- as.data.frame(cbind(get.edgelist(h, names = FALSE), E(h)$weight))
  # Endpoints, previous weight, and previous distance
  el <- cbind(el, t(sapply(1:dim(el)[1], function(i) {
    v1 <- el$V1[i]; v2 <- el$V2[i]
    c(if(are.connected(f, v1, v2)) E(f, c(v1, v2))$weight else 0,
      length(get.shortest.paths(f, from = v1, to = v2)[[1]]) - 1)
  })))
  names(el) <- c('v1', 'v2', 'count', 'weight', 'distance')
  el
}


# CHANGE POINT FITS

# Given a time series ts and a guess c, fit a change point model to ts
# with seed derived from the intersection of the linear fits to the data on
# either side of a specified point cp, and return the fit.
# (Setting the intercept at the intersection of the linear fits has been tried
# and doesn't work.)
cpm <- function(y, t = 1:length(y), cp = median(t)) {
  lm1 <- lm(y[t <= cp] ~ t[t <= cp])
  lm2 <- lm(y[t >= cp] ~ t[t >= cp])
  nls(
    formula = y ~ b + m1 * t + m2 * (t - c) * (t > c),
    start = list(
      b = lm1$coeff[1], m1 = lm1$coeff[2], m2 = lm2$coeff[2],
      c = - (lm1$coeff[1] - lm2$coeff[1]) / (lm1$coeff[2] - lm2$coeff[2])
    ),
    control = list(maxiter = 1000, minFactor = 1 / (2^64))
  )
}


# SIMPLIFY THIS!

# FUNCTION: Perform one-change point analysis for up to 5 dependent variables
multi.one.changepoint <- function(
  x,               # vector
  y,               # matrix or data frame with height = length(x)
  ch.ind = NULL,  # vector of length two in 1:length(x)
  ch.guess = NULL, # vector of length two between min(x) and max(x)
  norm = FALSE,    # normalize from best linear fit by residuals' std dev?
  alg = 'default', # or 'port' or 'plinear'
  plot = TRUE,     # produce images along the way?
  pchs = 16:20,     # plot style
  return.bmsd = FALSE # return normalization info also
) {
  stat.names <- colnames(y)
  xmin <- min(x)
  xmax <- max(x)
  xx <- rep(x, times = 5)
  y <- as.matrix(y)
  if(norm) {
    ynorm <- list()
    y.b.m.sd <- list()
    for(i in 1:dim(y)[2]) {
      ylm <- lm(y[,i] ~ x)
      yrs <- sd(resid(ylm))
      ynorm[[i]] <- (y[,i] - ylm$coeff[1] - ylm$coeff[2] * x) / yrs
      y.b.m.sd[[i]] <- c(ylm$coeff[1], ylm$coeff[2], yrs)
    }
    yy <- as.matrix(as.data.frame(ynorm))
  } else yy <- as.matrix(y)
  # Extend yy to 5 columns
  yy <- cbind(yy, as.data.frame(matrix(
    0,
    nrow = dim(y)[1],
    ncol = 5 - dim(y)[2]
  )))
  # Plot points
  if(plot) {
    cols <- rainbow(dim(y)[2])
    plot(
      xx[1:prod(dim(y))],
      as.matrix(yy[,1:dim(y)[2]]),
      pch = rep(pchs[1:dim(y)[2]], each = length(x)),
      col = rep(cols, each = length(x))
    )
  }
  # If no change index given, pick approximate midpoint
  if(length(ch.ind) != 1) {
    if(length(ch.guess) != 1) ch.ind <- floor(length(x) * 1 / 2) + 1
    else ch.ind <- sapply(ch.guess, function(cp) {
      min(which(x >= cp))
    })
  }
  # Starting values of change point
  c.i <- xmin + (xmax - xmin) * (ch.ind - 1) / (length(x) - 1)
  ch.ind <- sapply(c.i, function(c) which(x == ceiling(c)))
  #print(ch.ind)
  # Starting coefficient values
  b.i <- as.matrix(as.data.frame(lapply(1:5, function(i) {
    lm1 <- lm(yy[1:(ch.ind - 1),i] ~ x[1:(ch.ind - 1)])
    yint <- lm1$coeff[1] + lm1$coeff[2] * c.i
    yy2 <- yy[ch.ind:length(x),i] - yint
    xx2 <- x[ch.ind:length(x)] - c.i
    lm2 <- lm(yy2 ~ xx2 + 0)
    return(c(
      lm1$coeff[1], lm1$coeff[2], lm2$coeff[1] - lm1$coeff[2]
    ))
  })))
  # Plot linear fits between change points
  if(plot) {
    for(i in 1:dim(y)[2]) {
      lines(
        x = c(xmin, c.i),
        y = b.i[1,i] + b.i[2,i] * c(xmin, c.i),
        col = cols[i]
      )
      lines(
        x = c(c.i,xmax),
        y = b.i[1,i] - b.i[3,i] * c.i +
            (b.i[2,i] + b.i[3,i]) * c(c.i, xmax),
        col = cols[i]
      )
    }
    abline(v = c.i, lty = 2)
  }
  stat.id <- rep(c(1:dim(y)[2], rep(0, 5 - dim(y)[2])), each = length(x))
  # List of names of coefficient variables for the linear fit
  b.names <- as.data.frame(lapply(1:5, function(i) {
    paste('b', 0:2, i, sep = '')
  }))
  # Formula strings
  fmla.strings <- lapply(1:dim(y)[2], function(i) {
    paste(
      '(', b.names[1,i], '+', b.names[2,i], '*', 'xx +',
      b.names[3,i], '* (xx - c1) * (xx >= c1))',
      '* (stat.id == ', i, ')',
      sep = '')
  })
  start.list <- list(
    c1 = c.i, b01 = b.i[1,1], b11 = b.i[2,1], b21 = b.i[3,1]
  )
  if(dim(y)[2] >= 2) start.list <- c(start.list, list(
    b02 = b.i[1,2], b12 = b.i[2,2], b22 = b.i[3,2]
  ))
  if(dim(y)[2] >= 3) start.list <- c(start.list, list(
    b03 = b.i[1,3], b13 = b.i[2,3], b23 = b.i[3,3]
  ))
  if(dim(y)[2] >= 4) start.list <- c(start.list, list(
    b04 = b.i[1,4], b14 = b.i[2,4], b24 = b.i[3,4]
  ))
  if(dim(y)[2] >= 5) start.list <- c(start.list, list(
    b05 = b.i[1,5], b15 = b.i[2,5], b25 = b.i[3,5]
  ))
  #print(fmla.strings)
  #print(start.list)
  yyy <- unlist(yy)
  model <- summary(nls(
    as.formula(paste('yyy ~', paste(fmla.strings, collapse = '+'))),
    start = start.list,
    control = list(maxiter = 1000, minFactor = 1 / (2 ^ 64)),
    algorithm = alg
  ))
  #print(model)
  # Save appropriate coefficients
  c.f <- model$coeff[1,1]
  b.f <- matrix(model$coeff[2:4,1], nc = 1)
  if(dim(y)[2] >= 2) b.f <- cbind(b.f, model$coeff[5:7,1])
  if(dim(y)[2] >= 3) b.f <- cbind(b.f, model$coeff[8:10,1])
  if(dim(y)[2] >= 4) b.f <- cbind(b.f, model$coeff[11:13,1])
  if(dim(y)[2] >= 5) b.f <- cbind(b.f, model$coeff[14:16,1])
  #print(b.f)
  # Print slopes of fits
  slopes <- list()
  for(i in 1:dim(y)[2]) slopes[[i]] <- c(
    b.f[2,i],
    b.f[2,i] + b.f[3,i]
  )
  if(norm) for(i in 1:dim(y)[2]) {
    slopes[[i]] <- slopes[[i]] * y.b.m.sd[[i]][3] + y.b.m.sd[[i]][2]
  }
  slopes <- as.data.frame(slopes)
  names(slopes) <- stat.names
  print('Slopes:')
  print(slopes)
  # Define fits
  fits <- list(function(X) {
    b.f[1,1] + b.f[2,1] * X +
    b.f[3,1] * (X - c.f) * (X >= c.f)
  })
  if(dim(y)[2] >= 2) fits <- c(fits, list(function(X) {
    b.f[1,2] + b.f[2,2] * X +
    b.f[3,2] * (X - c.f) * (X >= c.f)
  }))
  if(dim(y)[2] >= 3) fits <- c(fits, list(function(X) {
    b.f[1,3] + b.f[2,3] * X +
    b.f[3,3] * (X - c.f) * (X >= c.f)
  }))
  if(dim(y)[2] >= 4) fits <- c(fits, list(function(X) {
    b.f[1,4] + b.f[2,4] * X +
    b.f[3,4] * (X - c.f) * (X >= c.f)
  }))
  if(dim(y)[2] >= 5) fits <- c(fits, list(function(X) {
    b.f[1,5] + b.f[2,5] * X +
    b.f[3,5] * (X - c.f) * (X >= c.f)
  }))
  #print(fits)
  # Plot fits over points
  if(plot) {
    f <- fits[[1]]
    curve(
      f, from = min(x), to = max(x),
      ylim = c(min(yy), max(yy)), col = cols[1]
    )
    if(dim(y)[2] > 1) {
      for(i in 2:dim(y)[2]) {
        f <- fits[[i]]
        curve(f, from = min(x), to = max(x), add = TRUE, col = cols[i])
      }
    }
    points(
      xx[1:prod(dim(y))],
      unlist(yy[,1:dim(y)[2]]),
      pch = rep(pchs[1:dim(y)[2]], each = length(x)),
      col = rep(cols, each = length(x))
    )
    abline(v = c.f, lty = 2)
  }
  if(return.bmsd & norm) return(list(model = model, bmsd = y.b.m.sd))
  else if(return.bmsd) return(list(model = model, bmsd = c(0, 0, 1)))
  else return(model)
}

