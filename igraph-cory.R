# Basic igraph functions

library(igraph)


# Hall's criterion for the existence of a system of distinct representatives
hall.criterion <- function(lst) all(sapply(0:(2 ^ length(lst) - 1),
                                           function(i) {
    w <- which(intToBits(i) == 1)
    length(unique(unlist(lst[w]))) >= length(w)
}))


# BIJECTIONS BETWEEN POSITIVE INTEGERS AND BOUNDED PARTITIONS

# k-combination at a given rev-lex position
position.combination <- function(k, i) {
  vec <- c()
  N <- i
  for(j in k:1) {
    c <- j - 1
    while(choose(c + 1, j) <= N) c <- c + 1
    vec <- c(vec, c)
    N <- N - choose(c, j)
  }
  return(vec)
}

# Rev-lex position of a given k-combination of [0 : (n - 1)], k = length(vec)
combination.position <- function(vec) {
  stopifnot(!is.unsorted(rev(vec), strictly = TRUE))
  sum(choose(rev(vec), 1:length(vec)))
}

# Biject between combinations and partitions

# k-part partition corresponding to a given k-combination of [0 : (n - 1)]
combination.partition <- function(vec) vec - (length(vec) - 1):0

# k-combination of [0 : (n - 1)] corresponding to a given k-part partition
partition.combination <- function(lambda) lambda + (length(lambda) - 1):0

# Compose the bijections to biject between positions and partitions

# k-part partition at a given rev-lex position
position.partition <- function(k, i) {
  combination.partition(position.combination(k, i))
}

# Rev-lex position of a given k-part partition
partition.position <- function(lambda) {
  combination.position(partition.combination(lambda))
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

# CONSIDER CALCULATING NEIGHBORHOODS OF ALL PRIMARY NODES,
# AND PASSING THIS LIST TO THE WEDGES FUNCTION

# Wedges through a given node in a given two-mode network (classical)
classical.wedges <- function(bigraph, Q) {
    
}

# Wedges through a given node in a given two-mode network (Opsahl)
# Agrees globally and locally with bipartite.transitivity on four small networks
opsahl.wedges <- function(bigraph, Q) {
    # Identify secondary neighbors of Q
    n1 <- setdiff(neighborhood(bigraph, 1, Q)[[1]], Q)
    # If there aren't at least two, return zeroes
    if(length(n1) < 2) return(c(0, 0))
    # Identify primary neighborhoods of secondary neighbors of Q
    n1n1 <- lapply(neighborhood(bigraph, 1, n1), setdiff, c(Q, n1))
    # Array the 2-paths centered at Q
    # (Note that these are indices of n1n1, not vertex ids)
    p <- combn(1:length(n1), 2)
    # Across the pairs (X, Y) list the numbers of wedges and of closed wedges
    wedgelist <- do.call(cbind, lapply(1:dim(p)[2], function(j) {
        # The first node X must have a nonempty neighborhood besides Q
        if(length(n1n1[[p[1, j]]]) == 0) return(c(0, 0))
        # Across all choices of P from the non-Q primary neighbors of X
        do.call(cbind, lapply(n1n1[[p[1, j]]], function(P) {
            # The second node Y must have a nonempty nbhd besides Q and P
            Rs <- setdiff(n1n1[[p[2, j]]], P)
            if(length(Rs) == 0) return(c(0, 0))
            # Which Rs produce 4-paths (P, X, Q, Y, R) that are closed?
            Rw <- which(sapply(Rs, function(R) {
                length(setdiff(intersect(neighborhood(bigraph, 1, P)[[1]],
                                         neighborhood(bigraph, 1, R)[[1]]),
                               n1[p[, j]])) > 0
            }))
            return(c(length(Rs), length(Rw)))
        }))
    }))
    return(rowSums(wedgelist))
}

# Wedges through a given node in a given two-mode network (inclusive)
incl.wedges <- function(bigraph, Q) {
    # Identify nodes of separation (exactly) 1 and 2 from v
    n1 <- setdiff(neighborhood(bigraph, 1, Q)[[1]], Q)
    n2 <- setdiff(neighborhood(bigraph, 2, Q)[[1]], c(n1, Q))
    # Require at least two nodes of separation 2 for a wedge
    if(length(n2) < 2) return(c(0, 0))
    # Identify pairs (P, R) of nodes in n2
    p <- combn(n2, 2)
    # Identify which of these pairs form wedges and, of these, which are closed
    wedgelist <- sapply(1:dim(p)[2], function(j) {
        # Secondary neighbors of P and of R
        pn1 <- neighborhood(bigraph, 1, p[1:2, j])
        # Common neighbors of P and R
        tn1 <- do.call(intersect, pn1)
        # If only one secondary links either to Q then no wedges exist
        if(length(intersect(n1, unique(unlist(pn1)))) == 1) c(0, 0) else
            # Otherwise one wedge, closed iff Hall criterion is met
            c(1, as.numeric(hall.criterion(list(intersect(n1, pn1[[1]]),
                                                intersect(n1, pn1[[2]]),
                                                tn1))))
    })
    return(rowSums(wedgelist))
}

# Wedges through a given node in a given two-mode network (exclusive)
excl.wedges <- function(bigraph, Q) {
    # Identify nodes of separation (exactly) 1 and 2 from v
    n1 <- setdiff(neighborhood(bigraph, 1, Q)[[1]], Q)
    n2 <- setdiff(neighborhood(bigraph, 2, Q)[[1]], c(n1, Q)) # rm Q?
    # Require at least two nodes of separation 2 for a wedge
    if(length(n2) < 2) return(c(0, 0))
    # Identify secondary neighbors of primary neighbors P of Q (excluding P)
    n2n1 <- lapply(n2, function(P) setdiff(neighborhood(bigraph, 1, P)[[1]], P))
    # Identify indexes of pairs (P, R) of nodes in n2
    p <- combn(1:length(n2), 2)
    # Remove pairs (P, R) that have no pairwise exclusive secondary neighbors
    p <- as.matrix(p[, sapply(1:dim(p)[2], function(j) {
        (0 < length(setdiff(intersect(n2n1[[p[1, j]]], n1), n2n1[[p[2, j]]])) *
             length(setdiff(intersect(n2n1[[p[2, j]]], n1), n2n1[[p[1, j]]])))
    })], nr = 2)
    # Require at least two nodes of separation 2 for a wedge
    if(dim(p)[2] == 0) return(c(0, 0))
    # Identify which of these pairs share a neighbor not shared with Q
    cl <- sapply(1:dim(p)[2], function(j) {
        0 < length(setdiff(intersect(n2n1[[p[1, j]]], n2n1[[p[2, j]]]), n1))
    })
    # Return the counts
    return(c(length(cl), sum(cl)))
}

# Generic two-mode clustering coefficient
# (Progress bars don't work in apply functions; try pbapply package)
twomode.transitivity <- function(
    bigraph, node.type = 0, type = 'global', wedges.fn = opsahl.wedges,
    vids = which(V(bigraph)$type == node.type)
    ) {
    # Check that nodes are of the desired type
    stopifnot(all(V(bigraph)$type[vids] == node.type))
    # If global or both, need to look at all vertices
    Qs <- if(type != 'local') which(V(bigraph)$type == node.type) else vids
    # Array of 4-paths centered at each Q in Qs
    wedges <- matrix(unlist(lapply(Qs, function(Q) {
        # Return wedge and closed wedge counts at Q
        return(wedges.fn(bigraph, Q))
    })), nr = 2)
    if(type == 'global') return(sum(wedges[2, ]) / sum(wedges[1, ]))
    if(type == 'local') return(wedges[2, ] / wedges[1, ])
    return(data.frame(V = wedges[1, ], T = wedges[2, ]))
}

# Opsah'l clustering coefficient
opsahl.transitivity <- function(
    bigraph, node.type = 0, type = 'global',
    vids = which(V(bigraph)$type == node.type)
    ) {
    twomode.transitivity(
        bigraph = bigraph, node.type = node.type, type = type,
        wedges.fn = opsahl.wedges, vids = vids)
}

# Inclusive clustering coefficient
incl.transitivity <- function(
    bigraph, node.type = 0, type = 'global',
    vids = which(V(bigraph)$type == node.type)
    ) {
    twomode.transitivity(
        bigraph = bigraph, node.type = node.type, type = type,
        wedges.fn = incl.wedges, vids = vids)
}

# Exclusive clustering coefficient
excl.transitivity <- function(
    bigraph, node.type = 0, type = 'global',
    vids = which(V(bigraph)$type == node.type)
    ) {
    twomode.transitivity(
        bigraph = bigraph, node.type = node.type, type = type,
        wedges.fn = excl.wedges, vids = vids)
}


# FUNCTION: Triad census for undirected networks (only 4 isomorphism classes)
simple.triad.census <- function(graph, rcnames = FALSE) {
  tc <- triad.census(as.directed(graph))
  if(is.nan(tc[1])) tc[1] <- choose(vcount(graph), 3) - sum(tc, na.rm = TRUE)
  stc <- tc[c(1, 3, 11, 16)]
  if(rcnames) names(stc) <- 0:3
  return(stc)
}

# FUNCTION: Two-mode dyad census (equivalently, distribution of edge weights
# in the one-mode projection when edges are weighted by shared event count)
twomode.dyad.census <- function(bigraph, type = 0) {
    graph <- bipartite.projection(bigraph, multiplicity = TRUE)[[1 + type]]
    disconnected <- choose(vcount(graph), 2) - ecount(graph)
    return(c('0' = if(disconnected == 0) NULL else disconnected,
             table(E(graph)$weight)))
}

# FUNCTION: Produce a one-mode projection onto nodes of the given type
# so that the names of the projection nodes are the indices of their
# counterparts in the original bigraph
onemode.projection <- function(bigraph, type = 0, name = 'name') {
    if(name == 'id') V(bigraph)$name <- V(bigraph)
    return(bipartite.projection(bigraph, multiplicity = TRUE)[[1 + type]])
}

# FUNCTION: Tally disconnected triples with a single edge of weight x
one.tied.triads <- function(graph) {
    # Create a data frame of weights and number of nonadjacent nodes
    counts <- data.frame(
        x = E(graph)$weight,
        n = vcount(graph) - sapply(1:ecount(graph), function(i) {
            length(unique(unlist(neighborhood(graph, 1, get.edge(graph, i)))))
        })
    )
    # Return the aggregated data frame
    return(aggregate(n ~ x, data = counts, FUN = sum))
}

# FUNCTION: Count the secondary nodes shared by the given primary nodes
share.weight <- function(bigraph, vids, name = 'name') {
    if(name == 'id') vids <- as.numeric(vids)
    length(Reduce(intersect, neighborhood(bigraph, 1, as.numeric(vids))))
}

# FUNCTION: Return the weight of the edge between two nodes, or else zero
edge.weight <- function(graph, vp) {
    id <- get.edge.ids(graph, vp)
    if(id == 0) 0 else E(graph)$weight[id]
}

# FUNCTION: Count open and closed wedges, subtracting triad weight if nonzero
connected.triples <- function(
    bigraph, type = 0,
    # Construct the one-mode projection if it's not already prepared
    graph = onemode.projection(bigraph, type = type, name = 'id')
    ) {
    trips <- do.call(rbind, lapply(1:vcount(graph), function(i) {
        nbhd <- neighborhood(graph, 1, i)[[1]]
        # Skip nodes with not enough neighbors
        if(length(nbhd) < 2) return(NULL)
        # horizontal array of pairs of neighbors of i
        v <- combn(setdiff(nbhd, i), 2)
        # vector of triad weights
        w <- sapply(1:dim(v)[2], function(j) {
            share.weight(bigraph, V(graph)$name[c(i, v[, j])])
        })
        # horizontal array of sorted triples of edge weights
        ew <- sapply(1:dim(v)[2], function(j) {
            sort(c(edge.weight(graph, c(i, v[1, j])),
                   edge.weight(graph, c(i, v[2, j])),
                   edge.weight(graph, c(v[1, j], v[2, j]))),
                 decreasing = TRUE)
        })
        # vertical array of pair and triad weights
        return(data.frame(x = ew[1, ] - w, y = ew[2, ] - w,
                          z = ew[3, ] - w, w = w))
    }))
    return(aggregate(n ~ x * y * z * w, FUN = sum,
                     data = cbind(trips,
                                  n = 1 - (trips$z + trips$w > 0) * 2 / 3)))
}

# FUNCTION: Triad census for two-mode networks
# (Iterates over nodes)
twomode.triad.census1 <- function(bigraph, type = 0, rcnames = FALSE,
                                  verbose = FALSE) {
    # Drop trivial cases
    if(vcount(bigraph) == 0) return(matrix(0, nr = 0, nc = 0))
    # Create one-mode projection
    graph <- onemode.projection(bigraph, type = type, name = 'id')
    
    # Find maximum values of x and of w
    max.x <- max(E(graph)$weight)
    # Initialize matrix (overestimating the number of columns)
    C <- as.data.frame(matrix(0, nr = choose(max.x + 3, 3), nc = max.x + 1))
    
    # Tally one-tied triads
    ot <- one.tied.triads(graph)
    # Insert the totals at the proper entries of C
    # (No repeats, so no information loss)
    C[sapply(ot$x, function(x) partition.position(c(x, 0, 0))) + 1, 1] <- ot$n
    if(verbose) print('One-tied triads tallied')
    
    # Tally connected triples (be sure to specify consistent type)
    ct <- connected.triples(bigraph, type = type, graph = graph)
    # Trim any unnecessary columns
    max.w <- max(ct$w)
    C <- C[, 1:(max.w + 1)]
    # For each value of w:
    for(w in 0:max.w) {
        if(verbose) print(paste('Tallying weight-', w, ' connected triples',
                                sep = ''))
        # Which rows have weight w?
        rs <- which(ct$w == w)
        # Insert the totals at the proper rows in column w + 1 of C
        # (No repeats, so no information loss)
        C[sapply(rs, function(i) {
            partition.position(as.numeric(ct[i, 1:3])) + 1
        }), w + 1] <- ct$n[rs]
    }
    if(verbose) print('Connected triples tallied')
    
    # The remaining triads share no secondary nodes; count them as empty
    # (No triads should have yet been counted as empty)
    C[1, 1] <- choose(vcount(graph), 3) - sum(C)
    # Clear names
    colnames(C) <- NULL
    if(rcnames) {
        colnames(C) <- 0:(ncol(C) - 1)
        rownames(C) <- sapply(0:(nrow(C) - 1), function(i) paste(
            '(', paste(position.partition(i, k = 3), collapse = ','),
            ')', sep = ''))
    }
    return(as.matrix(C))
}

# FUNCTION: Tally triples with exactly two edges among them
two.tied.triads <- function(graph) {
    # List of open wedges (shortest paths of length 2) up to reversal
    p2 <- do.call(cbind, lapply(V(graph)[1:(vcount(graph) - 1)], function(v) {
        d2 <- as.numeric(V(graph)[
            which(shortest.paths(graph, v, (v + 1):vcount(graph),
                                 weights = NA) == 2) + v
            ])
        gasp <- get.all.shortest.paths(graph, v, d2, weights = NA)[[1]]
        do.call(cbind, gasp[sapply(gasp, length) == 3])
    }))
    # Horizontal array of sorted edge weight pairs
    if(is.null(p2)) return(NULL) else  wedges <- sapply(
        1:dim(p2)[2],
        function(j) sort(c(edge.weight(graph, c(p2[1, j], p2[2, j])),
                           edge.weight(graph, c(p2[2, j], p2[3, j]))),
                         decreasing = TRUE))
    # Make wedges into a data frame
    wedges <- data.frame(x = wedges[1, ], y = wedges[2, ], n = 1)
    # Return the aggregated data frame
    return(aggregate(n ~ x * y, FUN = sum,
                     data = cbind(wedges, n = rep(1, n = dim(wedges)[1]))))
}

# FUNCTION: Tally triangles, subtracting triad weight if nonzero
three.tied.triads <- function(
    bigraph, type = 0,
    # Construct the one-mode projection if it's not already prepared
    graph = onemode.projection(bigraph, type = type, name = 'id')
) {
    # Triangles are 3-cliques in the one-mode projection
    t <- do.call(cbind, cliques(graph, min = 3, max = 3))
    # Vector of triad weights
    w <- sapply(1:dim(t)[2], function(j) {
        share.weight(bigraph, V(graph)$name[c(t[1, j], t[2, j], t[3, j])])
    })
    # Horizontal array of sorted triples of edge weights
    ew <- sapply(1:dim(t)[2], function(j) {
        sort(c(edge.weight(graph, c(t[1, j], t[2, j])),
               edge.weight(graph, c(t[2, j], t[3, j])),
               edge.weight(graph, c(t[1, j], t[3, j]))),
             decreasing = TRUE)
    })
    tris <- data.frame(x = ew[1, ] - w, y = ew[2, ] - w,
                       z = ew[3, ] - w, w = w)
    return(aggregate(n ~ x * y * z * w, data = cbind(tris, n = 1), FUN = sum))
}

# FUNCTION: Triad census for two-mode networks
# (Iterates over paths of length 2)
twomode.triad.census2 <- function(bigraph, type = 0, rcnames = FALSE,
                                  verbose = FALSE) {
    # Drop trivial cases
    if(vcount(bigraph) == 0) return(matrix(0, nr = 0, nc = 0))
    # Create one-mode projection
    graph <- onemode.projection(bigraph, type = type, name = 'id')
    
    # Find maximum values of x and of w
    max.x <- max(E(graph)$weight)
    # Initialize matrix (overestimating the number of columns)
    C <- as.data.frame(matrix(0, nr = choose(max.x + 3, 3), nc = max.x + 1))
    
    # Tally one-tied triads
    ot <- one.tied.triads(graph)
    # Insert the totals at the proper entries of C
    # (Aggregated, so no repeats, so no information loss)
    C[sapply(ot$x, function(x) partition.position(c(x, 0, 0))) + 1, 1] <- ot$n
    if(verbose) print('One-tied triads tallied')
    
    # Tally two-tied triads
    tt <- two.tied.triads(graph)
    # Insert the totals at the proper entries of C
    # (Aggregated, so no repeats, so no information loss)
    C[sapply(1:dim(tt)[1], function(i) {
        partition.position(c(tt[i, 1], tt[i, 2], 0))
    }) + 1, 1] <- tt$n
    if(verbose) print('Two-tied triads tallied')
    
    # Tally triangles
    tht <- three.tied.triads(bigraph, type = type, graph = graph)
    # Trim any unnecessary columns
    max.w <- max(tht$w)
    C <- C[, 1:(max.w + 1)]
    # For each value of w:
    for(w in 0:max.w) {
        if(verbose) print(paste('Tallying weight-', w, ' three-tied triads',
                                sep = ''))
        # Which rows have weight w?
        rs <- which(tht$w == w)
        # Insert the totals at the proper rows in column w + 1 of C
        # (No repeats, so no information loss)
        C[sapply(rs, function(i) {
            partition.position(as.numeric(tht[i, 1:3])) + 1
        }), w + 1] <- tht$n[rs]
    }
    if(verbose) print('Three-tied triads tallied')
    
    # The remaining triads share no secondary nodes; count them as empty
    # (No triads should have yet been counted as empty)
    C[1, 1] <- choose(vcount(graph), 3) - sum(C)
    # Reality check: The total triad tally should equal |V(graph)|-choose-3
    stopifnot(sum(C) == choose(vcount(graph), 3))
    # Clear names
    colnames(C) <- NULL
    if(rcnames) {
        colnames(C) <- 0:(ncol(C) - 1)
        rownames(C) <- sapply(0:(nrow(C) - 1), function(i) paste(
            '(', paste(position.partition(i, k = 3), collapse = ','),
            ')', sep = ''))
    }
    return(as.matrix(C))
}

# Trials on small networks indicate that version 2 is substantially faster;
# version 1 is retained as a check
twomode.triad.census <- twomode.triad.census2

# subquadratic triad census algorithm
# http://vlado.fmf.uni-lj.si/pub/networks/doc/triads/triads.pdf
# USE BINOMIAL COEFFICIENT ENUMERATION OF PARTITIONS IN A (w,3) BOX

nbrs <- function(graph, node) {
  setdiff(neighborhood(graph, order = 2, nodes = node)[[1]],
          neighborhood(graph, order = 1, nodes = node)[[1]])}
jnts <- function(graph, nodes) {
  intersect(neighborhood(graph, order = 1, nodes = nodes[1])[[1]],
            neighborhood(graph, order = 1, nodes = nodes[2])[[1]])}

bipartite.triad.census <- function(bigraph, type = 1) {
  actors <- which(V(bigraph)$type == type); lenactors <- length(actors)
  if(lenactors == 0) return(NULL)
  unigraph <- bipartite.projection(bigraph)[[1 + type]]
  stopifnot(lenactors == vcount(unigraph))
  wts <- E(unigraph)$weight; if(is.null(wts)) return(NULL)
  len <- max(wts) + 1
  C <- list()
  mat <- sapply(0:(len-1), function(a) sapply(0:a, function(b) {
    sapply(0:b, function(c) {
      C[[a * len^2 + b * len + c + 1]] <<- rep(0, len)
      names(C)[a * len^2 + b * len + c + 1] <<- paste(a, b, c, sep = '-') })}))
  mat <- sapply(actors, function(v) {
    Rv <- nbrs(bigraph, v)
    sapply(Rv[Rv > v], function(u) { # v < u
      Ru <- nbrs(bigraph, u)
      WX <- jnts(bigraph, c(v, u)); lenWX <- length(WX)
      S <- setdiff(union(Rv, Ru), c(v, u))
      C[[lenWX * len^2 + 1]][1] <<- C[[lenWX * len^2 + 1]][1] +
        lenactors - length(S) - 2
      sapply(S[(u < S) | ((v < S) & (S < u) & !(S %in% Rv))], function(w) {
        WY <- jnts(bigraph, c(v, w)); lenWY <- length(WY)
        WZ <- jnts(bigraph, c(u, w)); lenWZ <- length(WZ)
        W <- intersect(intersect(WX, WY), WZ); v3 <- length(W)
        v2 <- sort(c(lenWX - v3, lenWY - v3, lenWZ - v3))
        C[[v2[3] * len^2 + v2[2] * len + v2[1] + 1]][v3 + 1] <<-
          C[[v2[3] * len^2 + v2[2] * len + v2[1] + 1]][v3 + 1] + 1 })})})
  # Turn the list rowwise into a matrix
  C <- t(do.call(cbind, C[which(sapply(C, length) > 0)]))
  C[1, 1] <- choose(lenactors, 3) - sum(C)
  # Check C[1, 1] against disconnected triad count on unipartite projection
  #stopifnot(C[1, 1] == simple.triad.census(unigraph)[1])
  # Label
  colnames(C) <- 0:(len - 1)
  # Remove unnecessarily high columns
  C <- C[, 1:max(which(colSums(C) > 0))]
  if(is.null(dim(C))) {
    C <- as.matrix(C, nc = 1)
    colnames(C) <- 0}
  return(C)}

# Derive clustering coefficients from two-mode triad census
tc2cc <- function(tc, S.fn, F.fn, num.denom = FALSE) {
  if(dim(tc)[1] * dim(tc)[2] == 0) return(NA)
  S.c <- sum(sapply(1:dim(tc)[2], function(j) sapply(1:dim(tc)[1], function(i) {
    if(tc[i, j] == 0) 0 else
    S.fn(position.partition(3, i - 1), j - 1) * tc[i, j]})))
  F.c <- sum(sapply(1:dim(tc)[2], function(j) sapply(1:dim(tc)[1], function(i) {
    if(tc[i, j] == 0) 0 else
    F.fn(position.partition(3, i - 1), j - 1) * tc[i, j]})))
  return(if(num.denom) c(S.c, S.c + F.c) else S.c / (S.c + F.c))}

# Classical clustering coefficient on the one-mode projection
# tc must be a matrix with rows indexed as partition.position
tc2C <- function(tc, num.denom = FALSE) tc2cc(tc,
  function(L, w) 3 * ((L[3] > 0) | (w > 0)),
  function(L, w) ((L[2] > 0) & (L[3] == 0) & (w == 0)), num.denom = num.denom)

# Global Opsahl clustering coefficient
# (agrees with bipartite.transitivity)
# tc must be a matrix with rows indexed as partition.position
tc2CO <- function(tc, num.denom = FALSE) tc2cc(tc,
  function(L, w) (L[1] * L[2] * (L[3] + w > 0) + L[1] * L[3] + L[2] * L[3] +
    L[1] * w * (L[2] > 0 | w > 1) + L[1] * w * (L[3] > 0 | w > 1) +
    L[2] * w + L[2] * w * (L[3] > 0 | w > 1) +
    2 * L[3] * w +
    2 * choose(w, 2) * max(3 * (w > 2), length(which(L > 0)))),
  function(L, w) (L[1] * L[2] * (L[3] + w == 0) +
    L[1] * (L[2] == 0 & w == 1) + L[1] * (L[3] == 0 & w == 1) +
    L[2] * (L[3] == 0 & w == 1) +
    2 * choose(w, 2) * min(3 * (w == 2), length(which(L == 0)))),
    num.denom = num.denom)

# Global inclusive clustering coefficient
# (existence of not necessarily induced 4-paths and 6-cycles)
# tc must be a matrix with rows indexed as partition.position
tc2Cin <- function(tc, num.denom = FALSE) tc2cc(tc,
  function(L, w) 3 * (length(which(L > 0)) + w > 2),
  function(L, w) (L[2] > 0 & L[3] == 0 & w == 0) +
    2 * (L[1] > 0 & L[2] == 0 & w == 1) +
    3 * (L[1] == 0 & w == 2),
  num.denom = num.denom)

# Global exclusive clustering coefficient
# (existence of induced 4-paths and 6-cycles)
# (agrees with exclusive.transitivity)
# tc must be a matrix with rows indexed as partition.position
tc2Cex <- function(tc, num.denom = FALSE) tc2cc(tc,
  function(L, w) 3 * (L[3] > 0),
  function(L, w) ((L[2] > 0) & (L[3] == 0)), num.denom)

# Pairwise weight-resolved exclusive clustering
# tc must be a matrix with rows indexed as partition.position
tc2Cexij <- function(tc, i, j, num.denom = FALSE) tc2cc(tc,
  function(L, w) 3 * ((L[2] >= i) & (L[3] >= j)),
  function(L, w) ((L[2] >= i) & (L[3] < j)), num.denom)

# Triad weight-resolved exclusive clustering
# tc must be a matrix with rows indexed as partition.position
tc2Cexw <- function(tc, ww, num.denom = FALSE) tc2cc(tc,
  function(L, w) 3 * ((L[3] > 0) & (w == ww)),
  function(L, w) ((L[2] > 0) & (L[3] == 0) & (w == ww)), num.denom)


# FUNCTION: Given MR data for window + increment, compute two vectors:
# L = vector indexed by node of number of pairs of unlinked neighbors in G_w
# C = vector indexed by node of number of these pairs linked in G_(w+i)
# Global proportion is sum(C) / sum(L)
# Average opportunity-dependent local proportion is
# sum(C[degree(g) == k]) / sum(L[degree(g) == k])
author.edgelist <- function(data) as.data.frame(t(matrix(unlist(lapply(
    authors(data),
    function(vec) if(length(vec) == 1) c() else combn(vec, m = 2)
  )), nr = 2)), stringsAsFactors = FALSE)
vee.closure <- function(data, window, increment) {
  el.0 <- author.edgelist(data[data$year %in% window, ])
  el.1 <- author.edgelist(data[data$year %in% increment, ])
  g.0 <- simplify(graph.data.frame(el.0, directed = FALSE))
  denom <- sum(sapply(neighborhood(g.0, order = 2), length) -
           degree(g.0) - 1) / 2
  el <- data.frame(V1 = c(el.0[, 1], el.1[, 1]),
                   V2 = c(el.0[, 2], el.1[, 2]),
                   old = c(rep(TRUE, dim(el.0)[1]), rep(FALSE, dim(el.1)[1])))
  g <- simplify(graph.data.frame(el, directed = FALSE),
                edge.attr.comb = list(old = any))
  E.new <- which(!E(g)$old)
  num <- sum(sapply(E.new, function(e) {
    ge <- get.edge(g, e)
    if(!(all(ge <= vcount(g.0)))) 0 else
    (shortest.paths(g.0, ge[1], ge[2]) == 2)
  }))
  num / denom
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

