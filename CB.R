node_k2 <- function (i, dag, data) {
  parents_i <- dag$nodes[[i]]$parents
  
  variations <- lengths(lapply(data, unique))
  r_i <- as.numeric(variations[i])
  
  
  
  if (length(parents_i) != 0){
    i_Values <- as.list(unique(data[[i]]))
    i_parentValues <- unique(data[parents_i])
    
    i_dataParents <- data[parents_i]
    
    i_string_setup <- paste("i_parentValues[", 1:length(i_parentValues[ ,1]), ",", sep="")
    
    i_string <- lapply(i_string_setup, function(x) paste("i_dataParents[," ,
                  1:length(parents_i), "]==",x ,1:length(parents_i), "]", sep = "", collapse = "&"))
    
    
    i_N_ij <- lapply(i_string, function(x) length(which(eval(parse(text=x)))))
    
    
    i_configurations<-as.list(unique(data[[i]]))
    i_configurations_string <- lapply(i_configurations,
                                      function(x) paste("& data$", i, "=='", x,"'", sep=""))
    
    
    i_parent_and_child_configurations <- outer(i_string,i_configurations_string, paste)
    i_N_ijk <- lapply(i_parent_and_child_configurations,
                      function(x) length(which(eval(parse(text=x)))))
    
  } 
  else {
    i_N_ij <- as.list(length(data[ ,1]))
    
    i_configurations<-as.list(unique(data[[i]]))
    i_configurations_string <- lapply(i_configurations,
                                      function(x) paste("data$", i, "=='", x,"'", sep="", collapse = "&"))
    
    i_N_ijk <- lapply(i_configurations_string,
                      function(x) length(which(eval(parse(text=x)))))
    
  } #else
  
  i_log_factorial_N_ijk <- lapply(i_N_ijk, lfactorial)
  
  i_total_log_factorial_N_ijk <- Reduce('+', i_log_factorial_N_ijk)
  
  i_first_sum_term <- lapply(i_N_ij, function(x) lfactorial(r_i - 1))
  
  i_total_first_sum_term <- Reduce('+', i_first_sum_term)
  
  i_second_sum_term <- lapply(i_N_ij, function(x) lfactorial(x + r_i -  1))
  
  i_total_second_sum_term <- Reduce('+', i_second_sum_term)
  
  score <- i_total_first_sum_term - i_total_second_sum_term + i_total_log_factorial_N_ijk
  
  
  return(score)
  
  
} #node_k2

#------------------------------------------------------------------------

k2_search_parent_scores <- function (dag, i, j, data) {
  dag <- set.arc(dag, from = j, to = i)
  score <- node_k2(i, dag, data)
  dag <- drop.arc(dag, from = j, to = i)
  return(score)
} #k2_search_parent_scores

# ----------------------------------------------------------------------


CB <- function(data, order, K2_bound = NULL, u = NULL,
               search = 'k2', score = 'k2', PCalpha = 0.05) {
  
  
  library(bnlearn)
  
  returns <- list()
  nodenames <- as.list(colnames(data))
  network_score <- -Inf
  score_improves <- TRUE
  ord <- 1
  if (is.null(K2_bound)) {
    K2_bound <- Inf
  }
  
  while (ord <= order & score_improves == TRUE) {
    
    pdag <- pc.stable(data, max.sx = ord, alpha = PCalpha)
    dag1 <- pdag
    ScoreDag <- dag1
    
    if (!is.null(u)) {
      degree_list <- list()
      for (node in nodes(dag1)) {
        degree_list <- append(degree_list, in.degree(dag1, node))
      }
      max_degree <- max(unlist(degree_list))
      if (max_degree > u) {
        too_dense <- TRUE
        print("Graph is too dense. Increasing size of conditioning sets")
      } else {
        too_dense <- FALSE
      }
    } 
    else {
      too_dense <- FALSE
    }
    
    
    if (too_dense == FALSE)
    {
      # This creates a list of all the undirected edges in the network
      undirectedEdges <- undirected.arcs(pdag)
      
      for (edge in 1:(length(undirectedEdges[,1])/2)) {
        
        i <-   undirectedEdges[[1,1]]
        j <-   undirectedEdges[[1,2]]
        
        check_i_to_j <- tryCatch(
          set.arc(dag1, from = i, to = j, check.cycles = TRUE),
          error = function(cond){     #print(cond)
            #print("Didn't add arc")
            #print(paste(i, " to ", j, " edge causes a cycle"))
            return(FALSE)},
          warning = function(cond) {  #print(cond)
            return(NULL)},
          finally = {})
        
        check_j_to_i <- tryCatch(
          set.arc(dag1, from = j, to = i, check.cycles = TRUE),
          error = function(cond){     #print(cond)
            #print("Didn't add arc")
            #print(paste(j, " to ", i, " edge causes a cycle"))
            return(FALSE)},
          warning = function(cond) {  #print(cond)
            return(NULL)},
          finally = {})
        
        if(class(check_i_to_j) != "bn"){
          dag1 <- set.arc(dag1, from = j, to = i, check.cycles = FALSE)
          #print("Oriented edge to prevent cycle")
        }
        else if (class(check_j_to_i) != "bn") {
          dag1 <- set.arc(dag1, from = i, to = j, check.cycles = FALSE)
          #print("Oriented edge to prevent cycle")
        }
        else {
          
          score_i <- node_k2(i, ScoreDag, data)
          score_j <- node_k2(j, ScoreDag, data)
          
          parents_i <- pdag$nodes[[i]]$parents
          parents_j <- pdag$nodes[[j]]$parents
          
          
          number_parents_i <- length(parents_i)
          number_parents_j <- length(parents_j)
          
          
          parents_i[number_parents_i + 1] <- j
          parents_j[number_parents_j + 1] <- i
          
          ScoreDag$nodes[[i]]$parents <- parents_i
          ScoreDag$nodes[[j]]$parents <- parents_j
          
          scoreParent_i <- node_k2(i, ScoreDag, data)
          scoreParent_j <- node_k2(j, ScoreDag, data)
          
          
          
          
          
          
          #Check this to make sure orientation is correct
          if((score_i * scoreParent_j) > (score_j * scoreParent_i)){
            dag1 <- set.arc(dag1, from = i, to = j, check.cycles = FALSE)
            #print(paste("Oriented edge from ", i , " to ", j, sep = ""))
          }
          else {
            dag1 <- set.arc(dag1, from = j, to = i, check.cycles = FALSE)
            #print(paste("Oriented edge from ", j , " to ", i, sep = ""))
          }
          
        }
        
        reduce_undirectedEdges <- which((undirectedEdges[,1] == i & undirectedEdges[,2] == j) |
                                          (undirectedEdges[,1] == j & undirectedEdges[,2] == i))
        
        undirectedEdges <- undirectedEdges[-c(reduce_undirectedEdges),]
        ScoreDag <- dag1
      }
      
      
      library(bnviewer)
      dag2 <- bn.to.igraph(dag1)
      
      
      library(igraph) 
      nodeorder <- topo_sort(dag2, mode = c("out"))
      nodenameorder <- list()
      for (nodenumber in nodeorder) {
        nodenameorder <- append(nodenameorder, nodenames[nodenumber])
      }
      
      
      dagK2 <- empty.graph(nodes(dag1))
      for (node in 2:length(nodenameorder)) {
        possible_Parents <- as.list(nodenameorder[1:(node-1)])
        i <- nodenameorder[[node]]
        score_Old <- node_k2(i, dagK2, data)
        scores <- lapply(possible_Parents, function(x) k2_search_parent_scores(dagK2, i, x, data))
        max_score <- max(unlist(scores))
        # print(paste("Old score is: ", score_Old, " | Max new score is: ", max_score))
        while (max_score > score_Old & in.degree(dagK2, i) < K2_bound) {
          parent_index <- which(scores==max_score)
          parent_to_add <- possible_Parents[[parent_index]]
          dagK2 <- set.arc(dagK2, from = parent_to_add, to = i)
          # print(paste("Old score is: ", score_Old, " | Max new score is: ", max_score))
          # print(paste("Adding edge from ", parent_to_add, " to ", i, sep = "" ))
          score_Old <- max_score
          possible_Parents[parent_index] <- NULL
          scores <- lapply(possible_Parents, function(x) k2_search_parent_scores(dagK2, i, x, data))
          max_score <- max(unlist(scores))
        }
        
      }
      
      new_score <- score(dagK2, data, type = 'k2')
      
      if (new_score > network_score) {
        network_score <- new_score
        score_improves <- TRUE
        ord <- ord + 1
        dag <- dagK2
      } else {
        score_improves <- FALSE
        #print(paste("Finished with order ", ord - 1))
        #print(paste("Previous Score: ", network_score, "  New Score: ", new_score, sep = ""))
      }
      
    } else {
      ord <- ord + 1
    }  
  }
  
  
  #graphviz.plot(dag, main = "DAG created after K2 Algorithm")
  
  
  returns$score <- network_score
  returns$network <- dag
  
  return(returns)
}


#CB(file = 'C:/Users/NJG/Desktop/ChestGenerated100819.csv', order = 5, K2_bound = 10, u = 15)
