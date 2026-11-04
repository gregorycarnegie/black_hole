pub const GEODESIC_WITH_CHECKS: &str = concat!(
    include_str!("../../assets/shaders/geodesic.wesl"),
    "\n",
    include_str!("../relativity.wesl")
);

pub fn compile_wesl(source: &str) -> String {
    let mut resolver = wesl::resolver::VirtualResolver::new();
    let path = "package::shader".parse().unwrap();
    resolver.add_module(path, source.into());
    resolver.add_module(
        "package::snapshot".parse().unwrap(),
        include_str!("../../assets/shaders/snapshot.wesl").into(),
    );
    resolver.add_module(
        "package::polarized_transfer".parse().unwrap(),
        include_str!("../../assets/shaders/polarized_transfer.wesl").into(),
    );
    resolver.add_module(
        "package::thermal".parse().unwrap(),
        include_str!("../../assets/shaders/thermal.wesl").into(),
    );
    resolver.add_module(
        "package::geodesic".parse().unwrap(),
        include_str!("../../assets/shaders/geodesic.wesl").into(),
    );
    wesl::Compiler::new(wesl::CompileOptions {
        visibility: false,
        ..Default::default()
    })
    .with_resolver(resolver)
    .compile("shader.wesl")
    .unwrap_or_else(|err| panic!("{}", err.diagnostic().render_plain()))
    .to_string()
}
