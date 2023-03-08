# this R script can be used to generate the graphs that are shown in the journal paper
require(ggplot2)
require(ggrepel)
require(dplyr)
require(tidyr)
require(ggthemes)
require(scales)
require(readr)

report.u1 <- read_table("report_u1.csv", 
    col_types = cols(K = col_number(), M = col_number(), 
        `Time(s)` = col_number()))

report.u2 <- read_table("report_u2.csv", 
    col_types = cols(K = col_number(), M = col_number(), 
        `Time(s)` = col_number()))

report.u3 <- read_table("report_u3.csv", 
    col_types = cols(K = col_number(), M = col_number(), 
        `Time(s)` = col_number()))

report.u4 <- read_table("report_u4.csv", 
    col_types = cols(K = col_number(), M = col_number(), 
        `Time(s)` = col_number()))

report.u1 = report.u1[-1,]
report.u2 = report.u2[-1,]
report.u3 = report.u3[-1,]
report.u4 = report.u4[-1,]

report = rbind(report.u1, report.u2, report.u3, report.u4)

report.semisafe = filter(report, Program == "semisafe")

G = apply(report.semisafe, 1, function(x){return (as.numeric(x[2]) * as.numeric(x[3]))})

report.semisafe = cbind(report.semisafe, G)

N = apply(report.semisafe, 1, function(x){if(as.numeric(x[3]) < 4){return (as.character(3))}else{return (as.character(4))}})

report.semisafe = cbind(report.semisafe, N)

L = apply(report.semisafe, 1, function(x){return (as.character(5 * as.numeric(x[10]) + as.numeric(x[2])))})

report.semisafe = cbind(report.semisafe, L)

Lab  = apply(report.semisafe, 1, function(x){return (paste("(", x[2], ",", x[3], ")", sep = ""))})

report.semisafe = cbind(report.semisafe, Lab)
colnames(report.semisafe)[5] = "Time"

# general code
q1 <- filter(report.semisafe, Formula == "02")
q1.table <- q1[, c(5,9,12)]
q1.table <- filter(q1.table, Time > 0)
pdf("journal_graphs\\q1.pdf")
ggplot(q1.table, aes(x=G, y=Time, label = Lab)) +
  geom_point() + geom_text_repel() + labs(y = "Time(s)")
dev.off()

q2 <- filter(report.semisafe, Formula == "04")
q2.table <- q2[, c(5,9,12)]
q2.table <- filter(q2.table, Time > 0)
pdf("journal_graphs\\q2.pdf")
ggplot(q2.table, aes(x=G, y=Time, label = Lab)) +
  geom_point() + geom_text_repel() + labs(y = "Time(s)")
dev.off()

q3 <- filter(report.semisafe, Formula == "05")
q3.table <- q3[, c(5,9,12)]
q3.table <- filter(q3.table, Time > 0)
pdf("journal_graphs\\q3.pdf")
ggplot(q3.table, aes(x=G, y=Time, label = Lab)) +
  geom_point() + geom_text_repel() + labs(y = "Time(s)")
dev.off()

q4 <- filter(report.semisafe, Formula == "06")
q4.table <- q4[, c(5,9,12)]
q4.table <- filter(q4.table, Time > 0)
pdf("journal_graphs\\q4.pdf")
ggplot(q4.table, aes(x=G, y=Time, label = Lab)) +
  geom_point() + geom_text_repel() + labs(y = "Time(s)")
dev.off()

q5 <- filter(report.semisafe, Formula == "07")
q5.table <- q5[, c(5,9,12)]
q5.table <- filter(q5.table, Time > 0)
pdf("journal_graphs\\q5.pdf")
ggplot(q5.table, aes(x=G, y=Time, label = Lab)) +
  geom_point() + geom_text_repel() + labs(y = "Time(s)")
dev.off()

q6 <- filter(report.semisafe, Formula == "08")
q6.table <- q6[, c(5,9,12)]
q6.table <- filter(q6.table, Time > 0)
pdf("journal_graphs\\q6.pdf")
ggplot(q6.table, aes(x=G, y=Time, label = Lab)) +
  geom_point() + geom_text_repel() + labs(y = "Time(s)")
dev.off()

q7 <- filter(report.semisafe, Formula == "09")
q7.table <- q7[, c(5,9,12)]
q7.table <- filter(q7.table, Time > 0)
pdf("journal_graphs\\q7.pdf")
ggplot(q7.table, aes(x=G, y=Time, label = Lab)) +
  geom_point() + geom_text_repel() + labs(y = "Time(s)") + scale_x_continuous(breaks = c(2,4,6,8,10,12))
dev.off()

q8 <- filter(report.semisafe, Formula == "11")
q8.table <- q8[, c(5,9,12)]
q8.table <- filter(q8.table, Time > 0)
pdf("journal_graphs\\q8.pdf")
ggplot(q8.table, aes(x=G, y=Time, label = Lab)) +
  geom_point() + geom_text_repel() + labs(y = "Time(s)")
dev.off()

q9 <- filter(report.semisafe, Formula == "13")
q9.table <- q9[, c(5,9,12)]
q9.table <- filter(q9.table, Time > 0)
pdf("journal_graphs\\q9.pdf")
ggplot(q9.table, aes(x=G, y=Time, label = Lab)) +
  geom_point() + geom_text_repel() + labs(y = "Time(s)")
dev.off()

q10 <- filter(report.semisafe, Formula == "14")
q10.table <- q10[, c(5,9,12)]
q10.table <- filter(q10.table, Time > 0)
pdf("journal_graphs\\q10.pdf")
ggplot(q10.table, aes(x=G, y=Time, label = Lab)) +
  geom_point() + geom_text_repel() + labs(y = "Time(s)")
dev.off()


# to generate the table of the results for each property
q1.table.alt <- q1[, c(2,3,5)]
q1.table.alt <- q1.table.alt %>% spread(M, Time)
q1.table.alt <- q1.table.alt[, -1]
write.csv(q1.table.alt,"tables\\q1.csv", row.names = TRUE)

q2.table.alt <- q2[, c(2,3,5)]
q2.table.alt <- q2.table.alt %>% spread(M, Time)
q2.table.alt <- q2.table.alt[, -1]
write.csv(q2.table.alt,"tables\\q2.csv", row.names = TRUE)

q3.table.alt <- q3[, c(2,3,5)]
q3.table.alt <- q3.table.alt %>% spread(M, Time)
q3.table.alt <- q3.table.alt[, -1]
write.csv(q3.table.alt,"tables\\q3.csv", row.names = TRUE)

q4.table.alt <- q4[, c(2,3,5)]
q4.table.alt <- q4.table.alt %>% spread(M, Time)
q4.table.alt <- q4.table.alt[, -1]
write.csv(q4.table.alt,"tables\\q4.csv", row.names = TRUE)

q5.table.alt <- q5[, c(2,3,5)]
q5.table.alt <- q5.table.alt %>% spread(M, Time)
q5.table.alt <- q5.table.alt[, -1]
write.csv(q5.table.alt,"tables\\q5.csv", row.names = TRUE)

q6.table.alt <- q6[, c(2,3,5)]
q6.table.alt <- q6.table.alt %>% spread(M, Time)
q6.table.alt <- q6.table.alt[, -1]
write.csv(q6.table.alt,"tables\\q6.csv", row.names = TRUE)

q7.table.alt <- q7[, c(2,3,5)]
q7.table.alt <- q7.table.alt %>% spread(M, Time)
q7.table.alt <- q7.table.alt[, -1]
write.csv(q7.table.alt,"tables\\q7.csv", row.names = TRUE)

q8.table.alt <- q8[, c(2,3,5)]
q8.table.alt <- q8.table.alt %>% spread(M, Time)
q8.table.alt <- q8.table.alt[, -1]
write.csv(q8.table.alt,"tables\\q8.csv", row.names = TRUE)

q9.table.alt <- q9[, c(2,3,5)]
q9.table.alt <- q9.table.alt %>% spread(M, Time)
q9.table.alt <- q9.table.alt[, -1]
write.csv(q9.table.alt,"tables\\q9.csv", row.names = TRUE)

q10.table.alt <- q10[, c(2,3,5)]
q10.table.alt <- q10.table.alt %>% spread(M, Time)
q10.table.alt <- q10.table.alt[, -1]
write.csv(q10.table.alt,"tables\\q10.csv", row.names = TRUE)