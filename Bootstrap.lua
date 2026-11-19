-- HereBeDragons-Pins hooks WorldMapFrame as soon as it loads. On some clients the map is
-- load-on-demand, so make sure it exists before the library file runs (Olympus\Bootstrap.lua).
if not WorldMapFrame then
	local load = (C_AddOns and C_AddOns.LoadAddOn) or LoadAddOn
	if load then pcall(load, "Blizzard_WorldMap") end
end
