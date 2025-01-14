.DEFAULT_GOAL:= all

fvt10:
	cargo xtask verify --targets fvt10-pt-cursor-navigation

fvt11:
	cargo xtask verify --targets fvt11-pt-cursor-guards

all:
	cargo xtask compile --targets vstd_extra
	cargo xtask compile --targets aster_common
	cargo xtask verify --targets fvt10-pt-cursor-navigation
	cargo xtask verify --targets fvt11-pt-cursor-guards
