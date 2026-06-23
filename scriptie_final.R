# scriptie_final.R
# Bachelor Thesis: Estimating Policy Interdependence
# A Spatial Econometric Analysis of Global Cybersecurity Strategy Diffusion
#
# Author:     Anna Heck
# Supervisor: Kees Jan van Garderen
# University of Amsterdam, June 2026
#
# Model overview:
#   M1  W_geo      cross-section 2015
#   M2  W_io       cross-section 2015
#   M3  W_geo      cross-section 2024
#   M4  W_io       cross-section 2024
#   M5  W_geo      panel 1FE
#   M6  W_io       panel 1FE
#   M7  W_io_bin   panel 1FE (robustness)
#   M8  W_geo      panel TWFE
#   M9  W_io       panel TWFE
#   M10 W_regional panel 1FE
#   M11 W_regional panel TWFE  <- main finding

# --- Packages ---
library(tidyverse)
library(sf)
library(spdep)
library(spatialreg)
library(splm)
library(Matrix)
library(countrycode)
library(data.table)
library(WDI)
library(texreg)
sf_use_s2(FALSE)
set.seed(42) # for reproducibility of Monte Carlo standard errors

# --- Working directory ---
setwd("C:/Users/annal/OneDrive/Documenten/Scriptie Econometrie")

# --- NCS data ---
ncs_raw <- fread(
  "ncs_data/National-Cybersecurity-Strategy-Data-main/data/inaugural_cybstrategies_2000_2024.csv"
)
ncs_adopt <- ncs_raw %>%
  rename(iso3 = Countries, adopt_year = Year) %>%
  select(iso3, adopt_year) %>%
  filter(!is.na(adopt_year), adopt_year >= 2000, adopt_year <= 2024)

# --- World Bank controls ---
wb_raw <- WDI(
  country   = "all",
  indicator = c(gdp = "NY.GDP.PCAP.KD",
                internet = "IT.NET.USER.ZS",
                pop = "SP.POP.TOTL"),
  start = 2000, end = 2024, extra = FALSE
)
wb_data <- wb_raw %>%
  mutate(iso3 = countrycode(iso2c, "iso2c", "iso3c")) %>%
  filter(!is.na(iso3)) %>%
  select(iso3, year, gdp, internet, pop) %>%
  mutate(log_gdp = log(gdp), log_pop = log(pop))

# --- COW IGO data ---
igo_raw <- fread(
  "state_year_formatv3.csv"
)
meta_cols <- c("ccode", "year", "state", "country")
igo_names <- setdiff(names(igo_raw), meta_cols)
igo_long <- igo_raw %>%
  select(all_of(c("ccode", "year", igo_names))) %>%
  filter(year >= 2000, year <= 2024) %>%
  mutate(iso3 = countrycode(ccode, "cown", "iso3c", warn = FALSE)) %>%
  filter(!is.na(iso3)) %>%
  select(-ccode)
igo_max_yr <- max(igo_long$year)

# --- Shapefile and W_geo ---
world_sf <- st_read("shapefile/ne_110m_admin_0_countries.shp", quiet = TRUE) %>%
  mutate(iso3 = case_when(ISO_A3 %in% c("-99", "-90") ~ NA_character_,
                          TRUE ~ ISO_A3)) %>%
  filter(!is.na(iso3))
nb_geo <- poly2nb(world_sf, queen = TRUE)
no_neigh <- which(card(nb_geo) == 0)
if (length(no_neigh) > 0) {
  world_sf <- world_sf[-no_neigh, ]
  nb_geo   <- poly2nb(world_sf, queen = TRUE)
}
listw_geo_full <- nb2listw(nb_geo, style = "W", zero.policy = TRUE)
W_geo_full_mat <- listw2mat(listw_geo_full)
rownames(W_geo_full_mat) <- colnames(W_geo_full_mat) <- world_sf$iso3

# --- Helper functions ---
build_W_io <- function(igo_year_data, countries_list) {
  d <- igo_year_data %>% filter(iso3 %in% countries_list) %>% arrange(iso3)
  M <- d %>% select(-year, -iso3) %>%
    mutate(across(everything(), ~ pmax(., 0L))) %>% as.matrix()
  rownames(M) <- d$iso3
  C  <- M %*% t(M); diag(C) <- 0
  rs <- rowSums(C); rs[rs == 0] <- 1
  (C / rs)[countries_list, countries_list]
}

build_C_io <- function(igo_year_data, countries_list) {
  d <- igo_year_data %>% filter(iso3 %in% countries_list) %>% arrange(iso3)
  M <- d %>% select(-year, -iso3) %>%
    mutate(across(everything(), ~ pmax(., 0L))) %>% as.matrix()
  rownames(M) <- d$iso3
  C <- M %*% t(M); diag(C) <- 0
  C[countries_list, countries_list]
}

restd <- function(W) {
  diag(W) <- 0
  rs <- rowSums(W); rs[rs == 0] <- 1
  W / rs
}

get_lambda <- function(m) {
  if (inherits(m, "splm")) {
    v <- NULL
    tryCatch({ raw <- m$arcoef
    if (!is.null(raw) && length(raw) > 0) v <- as.numeric(raw)[1] },
    error = function(e) NULL)
    if (is.null(v) || is.na(v))
      tryCatch({ raw <- coef(m, spatial = TRUE)
      if (!is.null(raw) && length(raw) > 0) v <- as.numeric(raw)[1] },
      error = function(e) NULL)
    if (is.null(v) || length(v) == 0) return(NA_real_)
    v <- suppressWarnings(as.numeric(v))[1]
    if (is.na(v) || abs(v) > 1.5) return(NA_real_)
    return(v)
  } else {
    val <- suppressWarnings(as.numeric(m$rho))[1]
    if (is.na(val) || abs(val) > 1.5) return(NA_real_)
    return(val)
  }
}

get_ll  <- function(m) {
  if (inherits(m, "splm")) return(as.numeric(m$logLik))
  as.numeric(logLik(m))
}
get_k <- function(m) {
  if (inherits(m, "splm")) return(length(m$coefficients) + 2L)
  attr(logLik(m), "df")
}
get_AIC <- function(m) -2 * get_ll(m) + 2 * get_k(m)
safe_val <- function(m, fn) {
  if (is.null(m)) NA_real_ else tryCatch(fn(m), error = function(e) NA_real_)
}

# --- Panel data and common country set ---
panel_full <- wb_data %>%
  left_join(ncs_adopt, by = "iso3") %>%
  mutate(adoption = case_when(!is.na(adopt_year) & adopt_year <= year ~ 1L,
                              TRUE ~ 0L)) %>%
  drop_na(log_gdp, internet, log_pop) %>%
  arrange(iso3, year)
common_all <- sort(Reduce(intersect, list(
  unique(panel_full$iso3), world_sf$iso3, unique(igo_long$iso3)
)))
panel_full <- panel_full %>% filter(iso3 %in% common_all)
world_sf   <- world_sf   %>% filter(iso3 %in% common_all) %>% arrange(iso3)
cat("Common countries:", length(common_all), "\n")

# --- Cross-section samples (2015 and 2024) ---
YEAR_CS1 <- 2015; YEAR_CS2 <- 2024
cs_countries <- panel_full %>%
  filter(year %in% c(YEAR_CS1, YEAR_CS2)) %>%
  group_by(iso3) %>% filter(n() == 2) %>% ungroup() %>%
  pull(iso3) %>% unique() %>% intersect(common_all) %>% sort()
cs_2015 <- panel_full %>% filter(year == YEAR_CS1, iso3 %in% cs_countries) %>% arrange(iso3)
cs_2024 <- panel_full %>% filter(year == YEAR_CS2, iso3 %in% cs_countries) %>% arrange(iso3)

W_geo_cs_raw <- W_geo_full_mat[cs_countries, cs_countries]
zero_geo <- rowSums(W_geo_cs_raw) == 0
if (any(zero_geo)) {
  cs_countries <- cs_countries[!zero_geo]
  cs_2015 <- cs_2015 %>% filter(iso3 %in% cs_countries)
  cs_2024 <- cs_2024 %>% filter(iso3 %in% cs_countries)
  W_geo_cs_raw <- W_geo_cs_raw[cs_countries, cs_countries]
}
W_geo_cs  <- restd(W_geo_cs_raw)
lw_geo_cs <- mat2listw(W_geo_cs, style = "W", zero.policy = TRUE)

igo_yr_cs1 <- min(YEAR_CS1, igo_max_yr)
W_io_2015  <- build_W_io(filter(igo_long, year == igo_yr_cs1), cs_countries)
W_io_2024  <- build_W_io(filter(igo_long, year == igo_max_yr), cs_countries)
lw_io_2015 <- mat2listw(W_io_2015, style = "W", zero.policy = TRUE)
lw_io_2024 <- mat2listw(W_io_2024, style = "W", zero.policy = TRUE)
cat("Cross-section N:", length(cs_countries), "\n")

# --- Pre-estimation diagnostics ---
run_diagnostics <- function(data_cs, lw, label) {
  cat("\n", label, "\n")
  ols <- lm(adoption ~ log_gdp + internet + log_pop, data = data_cs)
  mt  <- moran.test(residuals(ols), lw, zero.policy = TRUE)
  cat(sprintf("  Moran's I = %.4f  (p = %.4f)\n", mt$estimate[1], mt$p.value))
  lmt <- tryCatch(
    lm.RStests(ols, lw, test = c("RSlag", "adjRSlag"), zero.policy = TRUE),
    error = function(e) NULL)
  if (!is.null(lmt)) {
    cat(sprintf("  LM        = %.4f  (p = %.4f)\n", lmt$RSlag$statistic, lmt$RSlag$p.value))
    cat(sprintf("  RLM*      = %.4f  (p = %.4f)\n", lmt$adjRSlag$statistic, lmt$adjRSlag$p.value))
  }
}
cat("\n--- Pre-estimation diagnostics ---\n")
run_diagnostics(cs_2015, lw_geo_cs,  "W_geo  | 2015")
run_diagnostics(cs_2015, lw_io_2015, "W_io   | 2015")
run_diagnostics(cs_2024, lw_geo_cs,  "W_geo  | 2024")
run_diagnostics(cs_2024, lw_io_2024, "W_io   | 2024")

# --- Models 1-4: Cross-sectional SAR ---
cat("\n--- Cross-sectional SAR models ---\n\n")
m1 <- lagsarlm(adoption ~ log_gdp + internet + log_pop,
               data = cs_2015, listw = lw_geo_cs, zero.policy = TRUE, method = "eigen")
cat("M1 (W_geo, 2015):\n"); print(summary(m1))
m2 <- lagsarlm(adoption ~ log_gdp + internet + log_pop,
               data = cs_2015, listw = lw_io_2015, zero.policy = TRUE, method = "eigen")
cat("M2 (W_io, 2015):\n"); print(summary(m2))
m3 <- lagsarlm(adoption ~ log_gdp + internet + log_pop,
               data = cs_2024, listw = lw_geo_cs, zero.policy = TRUE, method = "eigen")
cat("M3 (W_geo, 2024):\n"); print(summary(m3))
m4 <- lagsarlm(adoption ~ log_gdp + internet + log_pop,
               data = cs_2024, listw = lw_io_2024, zero.policy = TRUE, method = "eigen")
cat("M4 (W_io, 2024):\n"); print(summary(m4))

cat("\nPost-estimation Moran's I (cross-sections):\n")
for (chk in list(list(m1, lw_geo_cs, "M1 W_geo 2015"),
                 list(m2, lw_io_2015, "M2 W_io  2015"),
                 list(m3, lw_geo_cs,  "M3 W_geo 2024"),
                 list(m4, lw_io_2024, "M4 W_io  2024"))) {
  mt <- tryCatch(moran.test(residuals(chk[[1]]), chk[[2]], zero.policy = TRUE),
                 error = function(e) NULL)
  if (!is.null(mt))
    cat(sprintf("  %-18s  I = %7.4f  p = %.4f\n", chk[[3]], mt$estimate[1], mt$p.value))
}

# --- Panel data ---
full_panel <- panel_full %>%
  filter(iso3 %in% cs_countries, year >= 2010, year <= 2024) %>%
  group_by(iso3) %>% filter(n() == 15) %>% ungroup() %>%
  arrange(iso3, year)
N_pan <- n_distinct(full_panel$iso3)
T_pan <- n_distinct(full_panel$year)
panel_countries <- sort(unique(full_panel$iso3))
cat("\nBalanced panel: N =", N_pan, "x T =", T_pan, "=", nrow(full_panel), "obs\n")

W_geo_pan  <- restd(W_geo_full_mat[panel_countries, panel_countries])
lw_geo_pan <- mat2listw(W_geo_pan, style = "W", zero.policy = TRUE)

igo_pan_list <- lapply(2010:igo_max_yr, function(yr) {
  d <- igo_long %>% filter(year == yr, iso3 %in% panel_countries)
  if (nrow(d) > 0) build_W_io(d, panel_countries) else NULL
})
igo_pan_list <- Filter(Negate(is.null), igo_pan_list)
W_io_pan    <- restd(Reduce("+", igo_pan_list) / length(igo_pan_list))
lw_io_pan   <- mat2listw(W_io_pan, style = "W", zero.policy = TRUE)

C_pan_list <- lapply(2010:igo_max_yr, function(yr) {
  d <- igo_long %>% filter(year == yr, iso3 %in% panel_countries)
  if (nrow(d) > 0) build_C_io(d, panel_countries) else NULL
})
C_pan_list <- Filter(Negate(is.null), C_pan_list)
C_pan_avg  <- Reduce("+", C_pan_list) / length(C_pan_list)
TAU_COUNT  <- quantile(C_pan_avg[C_pan_avg > 0], 0.75)
W_io_pan_bin <- ifelse(C_pan_avg >= TAU_COUNT, 1.0, 0.0)
diag(W_io_pan_bin) <- 0
rownames(W_io_pan_bin) <- colnames(W_io_pan_bin) <- panel_countries
W_io_pan_bin <- restd(W_io_pan_bin)
lw_io_pan_bin <- mat2listw(W_io_pan_bin, style = "W", zero.policy = TRUE)

# --- Models 5-9: Panel SAR ---
cat("\n--- Panel SAR models (2010-2024) ---\n\n")
spml_run <- function(label, listw, effect = "individual") {
  cat(label, "\n")
  m <- tryCatch(
    spml(adoption ~ log_gdp + internet + log_pop,
         data = full_panel, index = c("iso3", "year"),
         listw = listw, lag = TRUE, spatial.error = "none",
         model = "within", effect = effect, zero.policy = TRUE),
    error = function(e) { cat("  FAILED:", e$message, "\n"); NULL })
  if (!is.null(m)) print(summary(m))
  cat("\n")
  m
}
m5 <- spml_run("M5 (W_geo, 1FE)",    lw_geo_pan)
m6 <- spml_run("M6 (W_io, 1FE)",     lw_io_pan)
m7 <- spml_run("M7 (W_io_bin, 1FE)", lw_io_pan_bin)
m8 <- spml_run("M8 (W_geo, TWFE)",   lw_geo_pan,   effect = "twoways")
m9 <- spml_run("M9 (W_io, TWFE)",    lw_io_pan,    effect = "twoways")

cat("Post-estimation Moran's I (panel, last period):\n")
for (chk in list(list(m5, lw_geo_pan,    "M5 W_geo 1FE"),
                 list(m6, lw_io_pan,     "M6 W_io  1FE"),
                 list(m7, lw_io_pan_bin, "M7 W_io_bin 1FE"),
                 list(m8, lw_geo_pan,    "M8 W_geo TWFE"),
                 list(m9, lw_io_pan,     "M9 W_io  TWFE"))) {
  if (is.null(chk[[1]])) next
  res_all  <- residuals(chk[[1]])
  res_last <- res_all[((N_pan * (T_pan - 1)) + 1):(N_pan * T_pan)]
  mt <- tryCatch(moran.test(res_last, chk[[2]], zero.policy = TRUE),
                 error = function(e) NULL)
  if (!is.null(mt))
    cat(sprintf("  %-20s  I = %7.4f  p = %.4f\n", chk[[3]], mt$estimate[1], mt$p.value))
}

# --- W_regional: select regional IGOs (5-50% membership share) ---
igo_ref <- igo_long %>% filter(year == igo_max_yr, iso3 %in% panel_countries)
igo_cols_available <- setdiff(names(igo_ref), c("iso3", "year"))
membership_share <- igo_ref %>%
  select(all_of(igo_cols_available)) %>%
  mutate(across(everything(), ~ as.numeric(. > 0))) %>%
  summarise(across(everything(), ~ mean(., na.rm = TRUE))) %>%
  pivot_longer(everything(), names_to = "igo", values_to = "share")
THRESH_LO <- 0.05
THRESH_HI <- 0.50
regional_igos <- membership_share %>%
  filter(share >= THRESH_LO, share <= THRESH_HI) %>%
  pull(igo)
cat(sprintf("\nRegional IGOs selected: %d (out of %d total)\n",
            length(regional_igos), nrow(membership_share)))

build_W_regional <- function(igo_year_data, countries_list, reg_cols) {
  available_cols <- intersect(reg_cols, names(igo_year_data))
  if (length(available_cols) == 0) return(NULL)
  d <- igo_year_data %>% filter(iso3 %in% countries_list) %>%
    arrange(iso3) %>% select(iso3, all_of(available_cols))
  M <- d %>% select(-iso3) %>%
    mutate(across(everything(), ~ pmax(as.numeric(.), 0))) %>% as.matrix()
  rownames(M) <- d$iso3
  C <- M %*% t(M); diag(C) <- 0
  rs <- rowSums(C); rs[rs == 0] <- 1
  W <- C / rs
  W[countries_list, countries_list]
}

regional_pan_list <- lapply(2010:igo_max_yr, function(yr) {
  d <- igo_long %>% filter(year == yr, iso3 %in% panel_countries)
  if (nrow(d) > 0) build_W_regional(d, panel_countries, regional_igos) else NULL
})
regional_pan_list <- Filter(Negate(is.null), regional_pan_list)
W_regional_pan  <- restd(Reduce("+", regional_pan_list) / length(regional_pan_list))
lw_regional_pan <- mat2listw(W_regional_pan, style = "W", zero.policy = TRUE)

# --- Models 10-11: W_regional ---
cat("\n--- W_regional models ---\n\n")
m10 <- spml_run("M10 (W_regional, 1FE)",  lw_regional_pan)
m11 <- spml_run("M11 (W_regional, TWFE)", lw_regional_pan, effect = "twoways")

cat("Post-estimation Moran's I (W_regional):\n")
for (chk in list(list(m10, "M10 1FE"), list(m11, "M11 TWFE"))) {
  if (is.null(chk[[1]])) next
  res_all  <- residuals(chk[[1]])
  res_last <- res_all[((N_pan * (T_pan - 1)) + 1):(N_pan * T_pan)]
  mt <- tryCatch(moran.test(res_last, lw_regional_pan, zero.policy = TRUE),
                 error = function(e) NULL)
  if (!is.null(mt))
    cat(sprintf("  %-12s  I = %7.4f  p = %.4f\n", chk[[2]], mt$estimate[1], mt$p.value))
}

# --- Spatial multiplier: delta method CI (Appendix K) ---
cat("\n--- Spatial multiplier, delta method CI (M11) ---\n")
if (!is.null(m11)) {
  lam_hat <- get_lambda(m11)

  # Extract SE(lambda) from summary()$CoefTable.
  # splm labels the spatial lag parameter "rho" in the CoefTable;
  # column 2 is the standard error (regardless of column name).
  se_lam <- tryCatch({
    ct      <- summary(m11)$CoefTable
    idx     <- grep("rho|lambda|phi|ar", rownames(ct), ignore.case = TRUE)
    col_se  <- grep("std|se|error", colnames(ct), ignore.case = TRUE)
    if (length(idx) > 0 && length(col_se) > 0)
      as.numeric(ct[idx[1], col_se[1]])
    else if (length(idx) > 0)
      as.numeric(ct[idx[1], 2])   # column 2 is SE in standard splm output
    else
      NA_real_
  }, error = function(e) NA_real_)

  # Fallback: verified value from model output
  if (!is.finite(se_lam) || se_lam <= 0) {
    se_lam <- 0.098
    cat("  Note: automatic SE extraction failed; using SE = 0.098 from model output\n")
  }

  # Delta method: g(lambda) = (1 - lambda)^{-1}, g'(lambda) = (1 - lambda)^{-2}
  m_hat    <- 1 / (1 - lam_hat)
  se_mhat  <- (1 - lam_hat)^(-2) * se_lam
  ci_lo    <- m_hat - 1.96 * se_mhat
  ci_hi    <- m_hat + 1.96 * se_mhat

  cat(sprintf("  lambda_hat  = %.4f  SE(lambda)  = %.4f\n", lam_hat, se_lam))
  cat(sprintf("  Multiplier  = (1 - %.4f)^{-1}   = %.4f\n", lam_hat, m_hat))
  cat(sprintf("  SE(mult)    = (1 - %.4f)^{-2} x %.4f = %.4f\n",
              lam_hat, se_lam, se_mhat))
  cat(sprintf("  95%% CI      = [%.3f, %.3f]  (reported: [1.03, 1.81])\n", ci_lo, ci_hi))
}

# --- Direct and indirect effects (Monte Carlo, R = 500) ---
cat("\n--- Direct and indirect effects ---\n\n")
for (chk in list(list(m1, lw_geo_cs,  "M1 W_geo 2015"),
                 list(m2, lw_io_2015, "M2 W_io  2015"),
                 list(m3, lw_geo_cs,  "M3 W_geo 2024"),
                 list(m4, lw_io_2024, "M4 W_io  2024"))) {
  cat(chk[[3]], "\n")
  tryCatch({
    imp <- impacts(chk[[1]], listw = chk[[2]], R = 500)
    print(summary(imp, zstats = TRUE, short = TRUE))
  }, error = function(e) cat("  failed:", e$message, "\n"))
  cat("\n")
}

# --- Lambda and AIC summary ---
cat("\n--- Lambda and AIC for all models ---\n")
for (chk in list(
  list(m1,  "M1  W_geo CS2015"),
  list(m2,  "M2  W_io  CS2015"),
  list(m3,  "M3  W_geo CS2024"),
  list(m4,  "M4  W_io  CS2024"),
  list(m5,  "M5  W_geo 1FE"),
  list(m6,  "M6  W_io  1FE"),
  list(m7,  "M7  W_io_bin 1FE"),
  list(m8,  "M8  W_geo TWFE"),
  list(m9,  "M9  W_io  TWFE"),
  list(m10, "M10 W_regional 1FE"),
  list(m11, "M11 W_regional TWFE")
)) {
  lam <- safe_val(chk[[1]], get_lambda)
  aic <- safe_val(chk[[1]], get_AIC)
  cat(sprintf("  %-22s  lambda = %+.4f  AIC = %.1f\n", chk[[2]], lam, aic))
}

# --- Robustness check: alternative W_regional thresholds (Appendix E) ---
cat("\n--- Robustness check: alternative thresholds ---\n")
robustness_thresholds <- list(
  list(lo = 0.05, hi = 0.40, label = "5-40%"),
  list(lo = 0.10, hi = 0.50, label = "10-50%"),
  list(lo = 0.10, hi = 0.40, label = "10-40%"),
  list(lo = 0.02, hi = 0.50, label = "2-50%")
)
robustness_results <- list()
for (spec in robustness_thresholds) {
  cat("\nThreshold:", spec$label, "\n")
  regional_igos_rob <- membership_share %>%
    filter(share >= spec$lo, share <= spec$hi) %>%
    pull(igo)
  rob_pan_list <- lapply(2010:igo_max_yr, function(yr) {
    d <- igo_long %>% filter(year == yr, iso3 %in% panel_countries)
    if (nrow(d) > 0) build_W_regional(d, panel_countries, regional_igos_rob) else NULL
  })
  rob_pan_list <- Filter(Negate(is.null), rob_pan_list)
  W_rob  <- restd(Reduce("+", rob_pan_list) / length(rob_pan_list))
  lw_rob <- mat2listw(W_rob, style = "W", zero.policy = TRUE)
  m_rob_1fe <- tryCatch(
    spml(adoption ~ log_gdp + internet + log_pop,
         data = full_panel, index = c("iso3", "year"),
         listw = lw_rob, lag = TRUE, spatial.error = "none",
         model = "within", effect = "individual", zero.policy = TRUE),
    error = function(e) { cat("  1FE failed\n"); NULL })
  m_rob_twfe <- tryCatch(
    spml(adoption ~ log_gdp + internet + log_pop,
         data = full_panel, index = c("iso3", "year"),
         listw = lw_rob, lag = TRUE, spatial.error = "none",
         model = "within", effect = "twoways", zero.policy = TRUE),
    error = function(e) { cat("  TWFE failed\n"); NULL })
  get_moran_last <- function(mod) {
    if (is.null(mod)) return(c(NA, NA))
    res_all  <- residuals(mod)
    res_last <- res_all[((N_pan * (T_pan - 1)) + 1):(N_pan * T_pan)]
    mt <- tryCatch(moran.test(res_last, lw_rob, zero.policy = TRUE),
                   error = function(e) NULL)
    if (is.null(mt)) return(c(NA, NA))
    c(mt$estimate[1], mt$p.value)
  }
  lam_1fe  <- safe_val(m_rob_1fe,  get_lambda)
  lam_twfe <- safe_val(m_rob_twfe, get_lambda)
  aic_1fe  <- safe_val(m_rob_1fe,  get_AIC)
  aic_twfe <- safe_val(m_rob_twfe, get_AIC)
  mi_1fe   <- get_moran_last(m_rob_1fe)
  mi_twfe  <- get_moran_last(m_rob_twfe)
  cat(sprintf("  1FE:  lambda = %+.4f  AIC = %.1f  Moran I = %.4f (p = %.4f)\n",
              lam_1fe,  aic_1fe,  mi_1fe[1],  mi_1fe[2]))
  cat(sprintf("  TWFE: lambda = %+.4f  AIC = %.1f  Moran I = %.4f (p = %.4f)\n",
              lam_twfe, aic_twfe, mi_twfe[1], mi_twfe[2]))
  robustness_results[[spec$label]] <- list(
    threshold = spec$label,
    n_igos    = length(regional_igos_rob),
    lam_1fe   = lam_1fe,  aic_1fe  = aic_1fe,
    lam_twfe  = lam_twfe, aic_twfe = aic_twfe
  )
}
cat("\nRobustness summary (for Appendix E):\n")
cat(sprintf("%-10s  %-5s  %-10s  %-10s  %-10s  %-10s\n",
            "Threshold", "IGOs", "lam_1FE", "AIC_1FE", "lam_TWFE", "AIC_TWFE"))
cat(sprintf("%-10s  %-5s  %-10s  %-10s  %-10s  %-10s\n",
            "5-50%", "187",
            sprintf("%+.4f", get_lambda(m10)), sprintf("%.1f", get_AIC(m10)),
            sprintf("%+.4f", get_lambda(m11)), sprintf("%.1f", get_AIC(m11))))
for (res in robustness_results) {
  cat(sprintf("%-10s  %-5d  %-10s  %-10s  %-10s  %-10s\n",
              res$threshold, res$n_igos,
              sprintf("%+.4f", res$lam_1fe),  sprintf("%.1f", res$aic_1fe),
              sprintf("%+.4f", res$lam_twfe), sprintf("%.1f", res$aic_twfe)))
}

# --- Falsification test: permutation of W_regional (TWFE) ---
# Randomly permute the rows and columns of W_regional together, breaking
# the network structure while preserving matrix statistics. Under a random W,
# lambda should be indistinguishable from zero if the observed result is genuine.
cat("\n--- Falsification test: permuted W_regional (TWFE) ---\n")
cat("Running 200 permutations -- this takes approximately 15 minutes\n")
set.seed(123)
N_PERM      <- 200
lambda_perm <- numeric(N_PERM)

for (i in seq_len(N_PERM)) {
  perm   <- sample(N_pan)
  W_perm <- restd(W_regional_pan[perm, perm])
  rownames(W_perm) <- colnames(W_perm) <- panel_countries
  lw_perm <- mat2listw(W_perm, style = "W", zero.policy = TRUE)
  
  m_perm <- tryCatch(
    spml(adoption ~ log_gdp + internet + log_pop,
         data    = full_panel,
         index   = c("iso3", "year"),
         listw   = lw_perm,
         lag     = TRUE,
         spatial.error = "none",
         model   = "within",
         effect  = "twoways",
         zero.policy = TRUE),
    error = function(e) NULL
  )
  
  lambda_perm[i] <- if (!is.null(m_perm)) get_lambda(m_perm) else NA_real_
  if (i %% 25 == 0) cat(sprintf("  %d / %d done\n", i, N_PERM))
}

lambda_obs  <- get_lambda(m11)
lambda_perm <- na.omit(lambda_perm)

cat(sprintf("\nObserved lambda (M11) : %.4f\n", lambda_obs))
cat(sprintf("Permutation mean      : %.4f\n",   mean(lambda_perm)))
cat(sprintf("Permutation SD        : %.4f\n",   sd(lambda_perm)))
cat(sprintf("Empirical p-value     : %.4f\n",   mean(lambda_perm >= lambda_obs)))
cat(sprintf("Valid permutations    : %d\n",     length(lambda_perm)))

# year fixed effects from M11: recover gamma_t via y* = y - lambda*Wy - X*beta

cat("\n--- Year fixed effects from M11 (W_regional, TWFE) ---\n")

lambda_m11 <- get_lambda(m11)

# Extract beta safely: coef() on splm may return λ + β together; grab by name
all_coef_m11 <- as.numeric(m11$coefficients)
names(all_coef_m11) <- names(m11$coefficients)
beta_m11 <- all_coef_m11[c("log_gdp", "internet", "log_pop")]
cat(sprintf("lambda = %.4f | beta: log_gdp=%.4f internet=%.4f log_pop=%.4f\n",
            lambda_m11, beta_m11["log_gdp"], beta_m11["internet"], beta_m11["log_pop"]))

panel_sorted <- full_panel %>% arrange(iso3, year)

# Build block-diagonal W (NT x NT)
W_block <- kronecker(diag(T_pan), W_regional_pan)
y_vec   <- panel_sorted$adoption
Wy_vec  <- as.numeric(W_block %*% y_vec)

# Covariate matrix (3 columns, same order as model formula)
X_mat <- matrix(c(panel_sorted$log_gdp,
                  panel_sorted$internet,
                  panel_sorted$log_pop),
                ncol = 3,
                dimnames = list(NULL, c("log_gdp", "internet", "log_pop")))

# Partial out SAR lag and covariates
y_star <- y_vec - lambda_m11 * Wy_vec - X_mat %*% beta_m11
panel_sorted$y_star <- as.numeric(y_star)

# OLS on y_star ~ country FE + year FE  ->  year coefficients = gamma_hat_t
fe_lm   <- lm(y_star ~ factor(iso3) + factor(year), data = panel_sorted)
yfe_idx <- grep("^factor\\(year\\)", names(coef(fe_lm)))
yfe_val <- coef(fe_lm)[yfe_idx]
yfe_yrs <- as.integer(sub("factor\\(year\\)", "", names(yfe_val)))

year_fe_df <- data.frame(
  year  = c(min(panel_sorted$year), yfe_yrs),
  gamma = c(0, as.numeric(yfe_val))
) %>% dplyr::arrange(year)

cat("\ngamma_hat_t (reference = 2010 = 0):\n")
print(year_fe_df, row.names = FALSE)

write.csv(year_fe_df, "year_fe_m11.csv", row.names = FALSE)
cat("Saved: year_fe_m11.csv\n")

# year FE plot (Appendix H)
events_df <- data.frame(
  year  = c(2013, 2015, 2017),
  label = c("Snowden revelations", "UN GGE consensus", "WannaCry attack")
) %>% dplyr::left_join(year_fe_df, by = "year")

p_yfe <- ggplot(year_fe_df, aes(x = year, y = gamma)) +
  geom_ribbon(aes(ymin = 0, ymax = pmax(gamma, 0)),
              fill = "grey80", alpha = 0.6) +
  geom_line(colour = "black", linewidth = 0.8) +
  geom_point(colour = "black", size = 2, shape = 21, fill = "white", stroke = 0.8) +
  geom_point(data = events_df, aes(x = year, y = gamma),
             colour = "black", size = 3, shape = 16) +
  geom_text(data = events_df, aes(x = year, y = gamma, label = label),
            colour = "black", size = 2.7, vjust = -1.2, fontface = "italic") +
  geom_hline(yintercept = 0, linetype = "dashed", colour = "grey50", linewidth = 0.4) +
  scale_x_continuous(breaks = 2010:2024) +
  scale_y_continuous(expand = expansion(mult = c(0.02, 0.15))) +
  labs(
    x = "Year",
    y = expression(hat(gamma)[t]~"(estimated year fixed effect)")
  ) +
  theme_classic(base_size = 11) +
  theme(
    axis.text.x  = element_text(angle = 45, hjust = 1, size = 9),
    axis.line    = element_line(colour = "grey40"),
    panel.grid.major.y = element_line(colour = "grey90", linewidth = 0.3)
  )

ggsave(
  "year_fe_plot.pdf",
  p_yfe, width = 6, height = 3.5, device = cairo_pdf
)
cat("Plot saved: year_fe_plot.pdf\n")

# descriptive statistics
cat("\n--- Descriptive statistics ---\n")

desc_vars <- full_panel %>%
  select(adoption, log_gdp, internet, log_pop)

desc_stats <- desc_vars %>%
  summarise(across(everything(), list(
    N    = ~ sum(!is.na(.)),
    Mean = ~ mean(., na.rm = TRUE),
    SD   = ~ sd(., na.rm = TRUE),
    Min  = ~ min(., na.rm = TRUE),
    Max  = ~ max(., na.rm = TRUE)
  ))) %>%
  pivot_longer(everything(),
               names_to  = c("Variable", ".value"),
               names_sep = "_(?=[^_]+$)") %>%
  mutate(across(where(is.numeric), ~ round(., 3)))

print(desc_stats, row.names = FALSE)

# adoption rate by year
cat("\nAdoption rate by year:\n")
adopt_by_year <- full_panel %>%
  group_by(year) %>%
  summarise(pct_adopted = round(mean(adoption) * 100, 1), .groups = "drop")
print(adopt_by_year, row.names = FALSE)

write.csv(desc_stats,    "desc_stats.csv",    row.names = FALSE)
write.csv(adopt_by_year, "adopt_by_year.csv", row.names = FALSE)
cat("Saved: desc_stats.csv, adopt_by_year.csv\n")

# adoption curve (Appendix I)
events_adopt <- data.frame(
  year  = c(2013, 2015, 2017),
  label = c("Snowden revelations", "UN GGE consensus", "WannaCry attack")
) %>% dplyr::left_join(adopt_by_year, by = "year")

p_adopt <- ggplot(adopt_by_year, aes(x = year, y = pct_adopted)) +
  geom_ribbon(aes(ymin = 0, ymax = pct_adopted),
              fill = "grey85", alpha = 0.8) +
  geom_line(colour = "black", linewidth = 0.8) +
  geom_point(colour = "black", size = 2, shape = 21, fill = "white", stroke = 0.8) +
  geom_point(data = events_adopt, aes(x = year, y = pct_adopted),
             colour = "black", size = 3, shape = 16) +
  geom_text(data = events_adopt, aes(x = year, y = pct_adopted, label = label),
            colour = "black", size = 2.7, vjust = -1.2, fontface = "italic") +
  scale_x_continuous(breaks = 2010:2024) +
  scale_y_continuous(limits = c(0, 100),
                     breaks = seq(0, 100, 20),
                     labels = function(x) paste0(x, "%"),
                     expand = expansion(mult = c(0, 0.12))) +
  labs(x = "Year", y = "Share of countries with NCS (%)") +
  theme_classic(base_size = 11) +
  theme(
    axis.text.x  = element_text(angle = 45, hjust = 1, size = 9),
    axis.line    = element_line(colour = "grey40"),
    panel.grid.major.y = element_line(colour = "grey90", linewidth = 0.3)
  )

ggsave(
  "adoption_curve.pdf",
  p_adopt, width = 6, height = 3.5, device = cairo_pdf
)
cat("Plot saved: adoption_curve.pdf\n")

# coef_plot: lambda per weight matrix (Appendix G)
lambda_plot_df <- data.frame(
  W_spec = factor(
    c("W[geo]", "W[geo]", "W[io]", "W[io]", "W[regional]", "W[regional]"),
    levels = c("W[geo]", "W[io]", "W[regional]")
  ),
  FE     = factor(c("1FE", "TWFE", "1FE", "TWFE", "1FE", "TWFE"),
                  levels = c("1FE", "TWFE")),
  model  = c("M5", "M8", "M6", "M9", "M10", "M11"),
  lambda = c(0.183,  0.037, 0.772, -0.178, 0.737, 0.297),
  se     = c(0.025,  0.027, 0.037,  0.208, 0.039, 0.098)
) %>%
  mutate(
    ci_lo = lambda - 1.96 * se,
    ci_hi = lambda + 1.96 * se,
    y_pos = as.numeric(W_spec) + ifelse(FE == "1FE", 0.15, -0.15)
  )

p_coef <- ggplot(lambda_plot_df,
                 aes(x = lambda, y = y_pos, shape = FE, fill = FE)) +
  geom_vline(xintercept = 0, linetype = "dashed",
             colour = "grey50", linewidth = 0.4) +
  geom_errorbarh(aes(xmin = ci_lo, xmax = ci_hi),
                 height = 0.07, colour = "grey30", linewidth = 0.5) +
  geom_point(size = 3, colour = "black", stroke = 0.7) +
  geom_text(aes(label = model), vjust = -1.1, size = 2.6, colour = "grey30") +
  scale_shape_manual(values = c("1FE" = 21, "TWFE" = 22), name = "Fixed effects") +
  scale_fill_manual(values  = c("1FE" = "black", "TWFE" = "white"),
                    name = "Fixed effects") +
  scale_y_continuous(
    breaks = 1:3,
    labels = parse(text = c("W[geo]", "W[io]", "W[regional]")),
    limits = c(0.5, 3.6)
  ) +
  labs(x = expression(hat(lambda)~"with 95% CI"), y = NULL) +
  coord_cartesian(xlim = c(-0.65, 1.05)) +
  theme_classic(base_size = 11) +
  theme(
    axis.line.y        = element_blank(),
    axis.ticks.y       = element_blank(),
    axis.text.y        = element_text(size = 10.5),
    panel.grid.major.x = element_line(colour = "grey92", linewidth = 0.3),
    legend.position    = "bottom",
    legend.title       = element_text(size = 9),
    legend.text        = element_text(size = 9)
  ) +
  guides(
    shape = guide_legend(override.aes = list(fill  = c("black", "white"),
                                             shape = c(21, 22))),
    fill  = "none"
  )

ggsave(
  "coef_plot.pdf",
  p_coef, width = 5.5, height = 3.8, device = cairo_pdf
)
cat("Plot saved: coef_plot.pdf\n")

# W_regional network map (Appendix J)
# Uses spData::world (ships with spdep, already loaded) + WDI country lookup
# — no new package installation required

w_mat <- spdep::listw2mat(lw_regional_pan)

conn_df <- data.frame(
  iso3    = rownames(w_mat),
  n_peers = as.integer(rowSums(w_mat > 0)),
  stringsAsFactors = FALSE
)

# ISO3 → ISO2 lookup via WDI (already loaded above)
iso_lookup <- WDI::WDI_data$country %>%
  dplyr::select(iso2c, iso3c) %>%
  dplyr::filter(nchar(iso2c) == 2, nchar(iso3c) == 3) %>%
  dplyr::distinct()

conn_df <- conn_df %>%
  dplyr::left_join(iso_lookup, by = c("iso3" = "iso3c"))

# spData::world ships with spdep and contains iso_a2 + sf geometry
data("world", package = "spData")

world_map <- world %>%
  dplyr::filter(iso_a2 != "AQ") %>%
  dplyr::left_join(conn_df, by = c("iso_a2" = "iso2c"))

p_wmap <- ggplot(world_map) +
  geom_sf(aes(fill = n_peers), colour = "white", linewidth = 0.08) +
  scale_fill_gradient(
    low      = "grey88",
    high     = "grey15",
    na.value = "grey96",
    name     = "Regional peers"
  ) +
  theme_void(base_size = 10) +
  theme(
    legend.position   = "right",
    legend.key.height = unit(0.8, "cm"),
    legend.text       = element_text(size = 8),
    legend.title      = element_text(size = 9)
  )

ggsave(
  "wregional_map.pdf",
  p_wmap, width = 7.5, height = 4.2, device = cairo_pdf
)
cat("Plot saved: wregional_map.pdf\n")