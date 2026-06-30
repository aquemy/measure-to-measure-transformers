-- provenance.lua: render the provenance convention identically in HTML and PDF.
--
-- In HTML the .from-paper / .our-work / .strengthen divs, the .cols/.col two-column wrapper, and the
-- .badge spans are styled by styles/provenance.css and pass through unchanged. In PDF this filter
-- maps them to the tcolorbox environments, paracol columns, and badge macros defined in
-- tex/provenance.tex, so both formats show the same boxed, attributed layout.

local box_env = {
  ["from-paper"] = "frompaper",
  ["our-work"]   = "ourwork",
  ["strengthen"] = "strengthen",
}

local function is_pdf()
  return quarto.doc.is_format("pdf")
end

function Div(el)
  if not is_pdf() then return nil end

  -- provenance boxes -> tcolorbox environments
  for cls, env in pairs(box_env) do
    if el.classes:includes(cls) then
      table.insert(el.content, 1, pandoc.RawBlock("latex", "\\begin{" .. env .. "}"))
      table.insert(el.content, pandoc.RawBlock("latex", "\\end{" .. env .. "}"))
      return el
    end
  end

  -- two-column comparison -> paracol (columns stack if paracol is unavailable)
  if el.classes:includes("cols") then
    local out = pandoc.List()
    out:insert(pandoc.RawBlock("latex", "\\begin{paracol}{2}"))
    local first = true
    for _, child in ipairs(el.content) do
      if child.t == "Div" and child.classes:includes("col") then
        if not first then
          out:insert(pandoc.RawBlock("latex", "\\switchcolumn"))
        end
        first = false
        for _, b in ipairs(child.content) do out:insert(b) end
      else
        out:insert(child)
      end
    end
    out:insert(pandoc.RawBlock("latex", "\\end{paracol}"))
    return out
  end
end

function Span(el)
  if not is_pdf() then return nil end
  if el.classes:includes("badge") then
    local macro = "badgeinformal"
    if el.classes:includes("ok") then macro = "badgeok"
    elseif el.classes:includes("axiom") then macro = "badgeaxiom"
    elseif el.classes:includes("open") then macro = "badgeopen" end
    local txt = pandoc.utils.stringify(el)
    return pandoc.RawInline("latex", "\\" .. macro .. "{" .. txt .. "}")
  end
end
